-------------------------- MODULE PlusCalTranslator --------------------------
EXTENDS Integers, Sequences, FiniteSets, Records, TLC, Strings

(*
This module specifies the translation from the abstract syntax tree (AST) of a
global-naming PlusCal algorithm into its corresponding TLA+ specification.
It is written to be executable by TLC, where the CONSTANT `AST` is the input.

The translation is modeled as a pipeline of transformations:
1. Explode: Structured statements (if, while) are "exploded" into a flatter
   control-flow graph using simple statements and labels.
2. Translate: The flattened AST is translated into an intermediate, structured
   representation of the TLA+ specification, defining guards and updates for
   each labeled action. This is where `pc` and `stack` variables are introduced.
3. Subscript: Expressions in the intermediate spec are rewritten to add
   subscripts for process-local variables (e.g., `v` becomes `v[self]`).
4. Generate: The final TLA+ specification components (Init, Next, Fairness, etc.)
   are constructed from the subscripted representation.

This specification is a model of the translator, not a real implementation.
Many details, like parsing and transforming expressions, are abstracted away
by treating expressions as opaque strings or structured records.

Limitations & Hacks:
- The PlusCal AST grammar is simplified. It assumes single-threaded processes.
- Label generation is simplistic and relies on a counter. It's a hack for
  modeling purposes and may not be robust for all cases.
- Expression handling is abstract. The "subscripting" stage just wraps
  expressions in a record to signify the transformation.
- The computation of UNCHANGED variables in the final TLA+ output is
  abstracted. A real translator would need to perform static analysis.
- The spec uses TLC!ToString for label generation, making it TLC-dependent.
*)

CONSTANTS
  \* The abstract syntax tree of the PlusCal algorithm.
  \* An AST is a record: [vars |-> {..}, procs |-> <<..>>]
  \* A process is a record: [id |-> "P1", vars |-> {"x"}, body |-> <<..>>]
  \* A statement is a record with a `type` field, e.g.,
  \* [type |-> "label", name |-> "L1"]
  \* [type |-> "assign", lhs |-> "v", rhs |-> "e"]
  \* [type |-> "if", test |-> "c", then |-> <<..>>, else |-> <<..>>]
  \* [type |-> "while", label |-> "L1", test |-> "c", body |-> <<..>>]
  \* [type |-> "await", cond |-> "c"]
  \* [type |-> "goto", target |-> "l"]
  \* [type |-> "call", target |-> "proc", ret |-> "l_ret"]
  \* [type |-> "return"]
  AST,

  \* The fairness option for the generated spec.
  \* One of: "none", "weak_proc", "weak_next", "strong_proc"
  Fairness

VARIABLES
  \* The state of the translation pipeline.
  stage,

  \* Intermediate and final results of the translation.
  exploded_ast,       \* AST after exploding structured statements.
  translated_spec,    \* Intermediate representation before subscripting.
  subscripted_spec,   \* Spec after adding subscripts for local vars.
  
  \* Final generated TLA+ specification components (as structured data).
  tla_init,
  tla_next,
  tla_fairness,
  tla_spec,
  tla_termination

vars == << stage, exploded_ast, translated_spec, subscripted_spec,
            tla_init, tla_next, tla_fairness, tla_spec, tla_termination >>

------------------------- HELPER OPERATORS -------------------------

Procs == {p.id : p \in AST.procs}
GlobalVars == AST.vars
AllLocalVars == UNION {p.vars : p \in AST.procs}
IsLocalVar(var, proc) == var \in proc.vars

----------------- STAGE 1: EXPLODE STRUCTURED STATEMENTS -----------------

RECURSIVE _ExplodeStmts(_)
_ExplodeStmts(args) ==
  LET stmts   == args[1]
      proc_id == args[2]
      lc      == args[3]
  IN
    IF stmts = <<>>
    THEN [stmts |-> <<>>, lc |-> lc]
    ELSE
      LET head == Head(stmts)
          tail == Tail(stmts)
      IN
        IF head.type = "if"
        THEN
          LET then_label == proc_id \o "_then_" \o ToString(lc)
              else_label == proc_id \o "_else_" \o ToString(lc + 1)
              end_label  == proc_id \o "_end_" \o ToString(lc + 2)
              lc1        == lc + 3

              then_exploded == _ExplodeStmts(<<head.then, proc_id, lc1>>)
              else_exploded == _ExplodeStmts(<<head.else, proc_id, then_exploded.lc>>)
              rest_exploded == _ExplodeStmts(<<tail, proc_id, else_exploded.lc>>)

              branch_stmt == [type |-> "branch", test |-> head.test,
                                then_target |-> then_label, else_target |-> else_label]
              then_block  == <<[type|->"label", name|->then_label]>> \o then_exploded.stmts \o <<[type|->"goto", target|->end_label]>>
              else_block  == <<[type|->"label", name|->else_label]>> \o else_exploded.stmts \o <<[type|->"goto", target|->end_label]>>
              end_block   == <<[type|->"label", name|->end_label]>>

          IN [ stmts |-> <<branch_stmt>> \o then_block \o else_block \o end_block \o rest_exploded.stmts,
               lc |-> rest_exploded.lc ]
        ELSIF head.type = "while"
        THEN
           LET loop_label == head.label
               body_label == loop_label \o "_body"
               end_label  == loop_label \o "_end"

               body_exploded == _ExplodeStmts(<<head.body, proc_id, lc>>)
               rest_exploded == _ExplodeStmts(<<tail, proc_id, body_exploded.lc>>)

               branch_stmt == [type |-> "branch", test |-> head.test,
                                 then_target |-> body_label, else_target |-> end_label]
               body_block  == <<[type|->"label", name|->body_label]>> \o body_exploded.stmts \o <<[type|->"goto", target|->loop_label]>>
               end_block   == <<[type|->"label", name|->end_label]>>

           IN [ stmts |-> <<branch_stmt>> \o body_block \o end_block \o rest_exploded.stmts,
                lc |-> rest_exploded.lc ]
        ELSE
           LET rest_exploded == _ExplodeStmts(<<tail, proc_id, lc>>)
           IN [ stmts |-> <<head>> \o rest_exploded.stmts,
                lc |-> rest_exploded.lc ]

ExplodeAST ==
  /\ stage = "start"
  /\ LET
       RECURSIVE MapProcs(_, _)
       MapProcs(procs, lc) ==
         IF procs = <<>> THEN [procs |-> <<>>, lc |-> lc]
         ELSE LET p == Head(procs)
                  rest == Tail(procs)
                  exploded == _ExplodeStmts(<<p.body, p.id, lc>>)
                  new_p == [p EXCEPT !.body = exploded.stmts]
                  rest_mapped == MapProcs(rest, exploded.lc)
              IN [ procs |-> <<new_p>> \o rest_mapped.procs,
                   lc |-> rest_mapped.lc ]
       new_procs_res == MapProcs(AST.procs, 0)
     IN exploded_ast' = [AST EXCEPT !.procs = new_procs_res.procs]
  /\ stage' = "exploded"
  /\ UNCHANGED <<translated_spec, subscripted_spec, tla_init, tla_next,
                 tla_fairness, tla_spec, tla_termination>>

------------------ STAGE 2: TRANSLATE TO INTERMEDIATE SPEC ------------------

\* Finds the label of the next statement after the one at `index`.
FindNextCodeLabel(body, index) ==
  LET next_idx = index + 1
  IN IF next_idx >= Len(body) THEN "Done"
     ELSE IF body[next_idx+1].type = "label" THEN body[next_idx+1].name
     ELSE FindNextCodeLabel(body, next_idx)

\* Translates a single statement into a structured action representation.
TranslateStmt(stmt, next_label) ==
  CASE stmt.type = "assign" ->
         [ type |-> "action", guard |-> "TRUE",
           body |-> [type |-> "assign", lhs |-> stmt.lhs, rhs |-> stmt.rhs],
           pc_update |-> [type |-> "label", val |-> next_label] ]
     | stmt.type = "await" ->
         [ type |-> "action", guard |-> stmt.cond,
           body |-> [type |-> "skip"],
           pc_update |-> [type |-> "label", val |-> next_label] ]
     | stmt.type = "goto" ->
         [ type |-> "action", guard |-> "TRUE", body |-> [type |-> "skip"],
           pc_update |-> [type |-> "label", val |-> stmt.target] ]
     | stmt.type = "branch" ->
         [ type |-> "action", guard |-> "TRUE", body |-> [type |-> "skip"],
           pc_update |-> [type |-> "ite", test |-> stmt.test,
                         then |-> stmt.then_target, else |-> stmt.else_target] ]
     | stmt.type = "call" ->
         [ type |-> "action", guard |-> "TRUE",
           body |-> [type |-> "call", ret |-> stmt.ret],
           pc_update |-> [type |-> "label", val |-> (CHOOSE p \in AST.procs: p.id = stmt.target).body[1].name] ]
     | stmt.type = "return" ->
         [ type |-> "action", guard |-> "TRUE",
           body |-> [type |-> "return"],
           pc_update |-> [type |-> "stack_top"] ]
     | OTHER -> [ type |-> "error", msg |-> "Unknown stmt type: " \o stmt.type ]

TranslateToSpec ==
  /\ stage = "exploded"
  /\ LET
       AllSpecVars == GlobalVars \cup AllLocalVars \cup {"pc", "stack"}
       TranslateProcBody(body) ==
         LET LabelsAndIndices == { i \in DOMAIN body : body[i].type = "label" }
         IN [ body[i].name \in { b.name : b \in {body[j] : j \in LabelsAndIndices} } |->
                LET idx == CHOOSE j \in LabelsAndIndices : body[j].name = body[i].name
                    code_stmt == body[idx+1] \* Assume code always follows label
                    next_label == FindNextCodeLabel(body, idx+1)
                IN TranslateStmt(code_stmt, next_label)
            ]
       ProcActions == [ p \in Procs |-> TranslateProcBody(
                          (CHOOSE proc \in exploded_ast.procs : proc.id = p).body) ]
       InitPC == [p \in Procs |-> (CHOOSE proc \in AST.procs : proc.id=p).body[1].name]
       InitStack == [p \in Procs |-> << >>]
     IN translated_spec' = [ vars |-> AllSpecVars,
                              init |-> [pc |-> InitPC, stack |-> InitStack],
                              actions |-> ProcActions ]
  /\ stage' = "translated"
  /\ UNCHANGED <<exploded_ast, subscripted_spec, tla_init, tla_next,
                 tla_fairness, tla_spec, tla_termination>>

------------------ STAGE 3: ADD SUBSCRIPTS FOR LOCAL VARS -------------------

\* Abstractly model the subscripting of an expression.
SubscriptExpr(expr, local_vars, self) ==
  [ type |-> "subscripted", expr |-> expr, locals |-> local_vars, self |-> self ]

SubscriptAction(action, proc, self) ==
  LET Sub(e) == SubscriptExpr(e, proc.vars, self)
  IN [ action EXCEPT
         !.guard = Sub(action.guard),
         !.body = CASE action.body.type = "assign" ->
                       [ action.body EXCEPT
                           !.lhs = IF IsLocalVar(action.body.lhs, proc)
                                   THEN Sub(action.body.lhs)
                                   ELSE action.body.lhs,
                           !.rhs = Sub(action.body.rhs) ]
                  | OTHER -> action.body,
        !.pc_update = CASE action.pc_update.type = "ite" ->
                           [action.pc_update EXCEPT !.test = Sub(action.pc_update.test)]
                      | OTHER -> action.pc_update ]

SubscriptSpec ==
  /\ stage = "translated"
  /\ LET
       SubProcs(p_id) ==
         LET proc == CHOOSE p \in exploded_ast.procs : p.id = p_id
             proc_actions == translated_spec.actions[p_id]
         IN [ label \in DOMAIN proc_actions |->
                SubscriptAction(proc_actions[label], proc, p_id) ]
     IN subscripted_spec' =
          [ translated_spec EXCEPT
              !.actions = [ p \in Procs |-> SubProcs(p) ] ]
  /\ stage' = "subscripted"
  /\ UNCHANGED <<exploded_ast, translated_spec, tla_init, tla_next,
                 tla_fairness, tla_spec, tla_termination>>

-------------------- STAGE 4: GENERATE FINAL TLA+ AST --------------------

GenerateTLA ==
  /\ stage = "subscripted"
  /\ LET
       \* ---- Init ----
       \* For local variables, Init is v' = [self \in Procs |-> InitVal]
       LocalVarInits  == { [ var |-> v, val |-> "default_init" ] : v \in AllLocalVars }
       GlobalVarInits == { [ var |-> v, val |-> "default_init" ] : v \in GlobalVars }
       PCInit    == [var |-> "pc",    val |-> translated_spec.init.pc]
       StackInit == [var |-> "stack", val |-> translated_spec.init.stack]
       init == GlobalVarInits \cup LocalVarInits \cup {PCInit, StackInit}

       \* ---- Next ----
       ActionToTLA(act, p_id, label) ==
         LET
             pc_guard == [type |-> "=", lhs |-> "pc[" \o p_id \o "]", rhs |-> label]
             body_tla ==
               CASE act.body.type = "assign" ->
                 [type |-> "assign", lhs |-> act.body.lhs, rhs |-> act.body.rhs]
               | act.body.type = "call" ->
                 [type |-> "stack_push", proc |-> p_id, val |-> act.body.ret]
               | act.body.type = "return" ->
                 [type |-> "stack_pop", proc |-> p_id]
               | act.body.type = "skip" -> "TRUE"
             pc_update_tla ==
               LET target ==
                 CASE act.pc_update.type = "label" -> act.pc_update.val
                    | act.pc_update.type = "stack_top" -> [type |-> "stack_top", proc |-> p_id]
                    | act.pc_update.type = "ite" -> [type |-> "ite", test |-> act.pc_update.test,
                                                    then |-> act.pc_update.then, else |-> act.pc_update.else]
               IN [type |-> "pc_update", proc |-> p_id, target |-> target]
         IN [type |-> "action", label |-> label, guard |-> act.guard,
             body |-> body_tla, pc_update |-> pc_update_tla]

       ProcNext(p_id) ==
         LET proc_actions = subscripted_spec.actions[p_id]
         IN [ type |-> "disj",
              clauses |-> { ActionToTLA(proc_actions[l], p_id, l)
                            : l \in DOMAIN proc_actions } ]
       
       next == [type |-> "exists", var |-> "self", set |-> "Procs", body |-> ProcNext("self")]
               
       \* ---- Fairness ----
       fairness ==
         CASE Fairness = "none" -> "TRUE"
            | Fairness = "weak_proc" ->
                [ type |-> "forall", var |-> "self", set |-> "Procs",
                  body |-> [type |-> "WF", vars |-> "vars", A |-> ProcNext("self")] ]
            | Fairness = "weak_next" ->
                [ type |-> "WF", vars |-> "vars", A |-> next ]
            | Fairness = "strong_proc" ->
                [ type |-> "forall", var |-> "self", set |-> "Procs",
                  body |-> [type |-> "SF", vars |-> "vars", A |-> ProcNext("self")] ]

       \* ---- Spec & Termination ----
       spec == [ type |-> "/\\",
                clauses |-> { [type |-> "Init"],
                              [type |-> "Box", body |-> [type |-> "Next"]],
                              [type |-> "Fairness"] } ]
       
       termination == [ type |-> "forall", var |-> "p", set |-> "Procs",
                        body |-> [type |-> "eventually",
                                  body |-> [type |-> "=", lhs |-> "pc[p]", rhs |-> "\"Done\"" ]]]

     IN /\ tla_init' = init
        /\ tla_next' = next
        /\ tla_fairness' = fairness
        /\ tla_spec' = spec
        /\ tla_termination' = termination
        /\ stage' = "done"
  /\ UNCHANGED <<exploded_ast, translated_spec, subscripted_spec>>

Stutter ==
  /\ stage = "done"
  /\ UNCHANGED vars

------------------------ TOP-LEVEL SPECIFICATION -------------------------

Init ==
  /\ stage = "start"
  /\ exploded_ast = [procs |-> <<>>]
  /\ translated_spec = [vars |-> {}, init |-> [x \in {} |-> ""], actions |-> [p \in {} |-> [l \in {} |-> ""]]]
  /\ subscripted_spec = translated_spec
  /\ tla_init = {}
  /\ tla_next = [type |-> "FALSE"]
  /\ tla_fairness = "TRUE"
  /\ tla_spec = [type |-> "FALSE"]
  /\ tla_termination = [type |-> "FALSE"]

Next ==
  \/ ExplodeAST
  \/ TranslateToSpec
  \/ SubscriptSpec
  \/ GenerateTLA
  \/ Stutter

Spec == Init /\ [][Next]_vars

\* A liveness property of the translator itself, ensuring it finishes.
TranslationCompletes == <> (stage = "done")

=============================================================================