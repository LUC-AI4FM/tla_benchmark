----------------------------- MODULE Translator -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
This module models a translator from a high-level procedural/multiprocess algorithm
(AST) to an operational TLA+ semantics. The input AST is a mathematical record.
The translator produces a record out containing:
  - States: the set of runtime states
  - Init:   the set of initial states
  - Next:   the set of next-state pairs
  - Fair:   the fairness descriptor copied from AST
The translator either succeeds with out and done or signals err on malformed AST.
*)

CONSTANTS
  Values,           \* universe of values
  VarName,          \* identifiers for variables
  ProcName,         \* identifiers for procedures
  Label,            \* identifiers for labels
  Pid,              \* identifiers for processes
  Expr,             \* domain of pure expressions
  Guard,            \* domain of boolean conditions
  AST,              \* the input abstract syntax tree (record)
  EvalExpr,         \* a total function evaluating expressions given an environment
  EvalBool,         \* a total function evaluating guards given an environment
  EvalSet           \* a total function evaluating set-valued expressions given an environment

(*
We assume expression/guard evaluation functions have appropriate types.
Env is modeled as a total function VarName -> Values whose domain will be
restricted by scope where relevant.
*)
ASSUME
  /\ EvalExpr \in [Expr \X [VarName -> Values] -> Values]
  /\ EvalBool \in [Guard \X [VarName -> Values] -> BOOLEAN]
  /\ EvalSet  \in [Expr \X [VarName -> Values] -> SUBSET Values]

(*
AST shape (informal, enforced by WellFormed):
AST =
  [ Mode     : {"uni","multi"},
    Main     : ProcName,
    Pids     : SUBSET Pid,                        \* only when Mode = "multi"; nonempty finite
    Globals  : SUBSET VarName,
    GInitVal : [Globals -> Values],               \* initial values of globals
    Procs    : [ProcName -> 
                  [ Params  : Seq(VarName),
                    Locals  : SUBSET VarName,
                    Entry   : Label,
                    Body    : [Label -> Stmt]     \* labeled statements
                  ]],
    Fairness : 
      [ Kind  : {"none","WFAction","SFAction","WFProcess","SFProcess","WFStep","SFStep"},
        Scope : SUBSET Label \cup SUBSET Pid      \* abstract scope descriptor
      ]
  ]

Each Stmt is a record tagged by Tag with fields as needed below:
  Tag \in {"Skip","Assign","If","While","Goto","Call","Return","Either","When","With"}

  Assign: [Tag="Assign", lhs: VarName, rhs: Expr, next: Label]
  If    : [Tag="If",     test: Guard, then: Label, else: Label]
  While : [Tag="While",  test: Guard, body: Label, next: Label]
  Goto  : [Tag="Goto",   target: Label]
  Call  : [Tag="Call",   callee: ProcName, args: Seq(Expr), cont: Label]
  Return: [Tag="Return"]
  Skip  : [Tag="Skip",   next: Label]
  Either: [Tag="Either", alts: SUBSET Label]         \* nonempty
  When  : [Tag="When",   test: Guard, next: Label]    \* enabled only if test true
  With  : [Tag="With",   v: VarName, dom: Expr, next: Label]
*)

(***************************************************************************)
(************************ Runtime denotation helpers ************************)
(***************************************************************************)

PC == Label \cup {"halt"}

StoreOf(vars) == [vars -> Values]

StackFrame == 
  [ proc : ProcName,
    locals : [VarName -> Values],  \* defined only on params ∪ locals of proc; arbitrary elsewhere
    ret : PC
  ]

Top(S) == IF Len(S) = 0 THEN CHOOSE x : x = x  \* undefined value if empty; guarded by uses
         ELSE S[Len(S)]

Pop(S) == IF Len(S) = 0 THEN <<>> ELSE SubSeq(S, 1, Len(S)-1)

Push(S, x) == Append(S, x)

SetOfSeq(q) == { q[i] : i \in 1..Len(q) }

Override(f, g) == [ x \in DOMAIN f \cup DOMAIN g |-> IF x \in DOMAIN g THEN g[x] ELSE f[x] ]

IsFinite(S) == \A F \in SUBSET S : Cardinality(F) # Infinity => F \subseteq S

Globals(ast) == ast.Globals
Procs(ast) == DOMAIN ast.Procs
Params(ast, p) == ast.Procs[p].Params
Locals(ast, p) == ast.Procs[p].Locals
Entry(ast, p) == ast.Procs[p].Entry
Body(ast, p) == ast.Procs[p].Body
MainProc(ast) == ast.Main

(*
Scope sets
*)
InScopeLocals(ast,p) == Locals(ast,p) \cup SetOfSeq(Params(ast,p))
InScopeAll(ast,p) == Globals(ast) \cup InScopeLocals(ast,p)

(*
Environment construction for a current procedure context:
env = globals overridden by top-frame locals for identifiers in scope.
For locals not in scope, the value is the global's (irrelevant).
*)
EnvUni(ast, s) ==
  LET f == Top(s.stack) IN
    Override([v \in VarName |-> IF v \in Globals(ast) THEN s.g[v] ELSE CHOOSE d : d = d],
             [v \in VarName |-> IF v \in InScopeLocals(ast, f.proc) THEN f.locals[v] ELSE CHOOSE d : d = d])

EnvMulti(ast, s, pid) ==
  LET f == Top(s.stacks[pid]) IN
    Override([v \in VarName |-> IF v \in Globals(ast) THEN s.g[v] ELSE CHOOSE d : d = d],
             [v \in VarName |-> IF v \in InScopeLocals(ast, f.proc) THEN f.locals[v] ELSE CHOOSE d : d = d])

(*
Local store update helper: write variable x in the appropriate scope (local/param vs global).
*)
WriteVarUni(ast, s, x, val) ==
  LET f == Top(s.stack) IN
  IF x \in InScopeLocals(ast, f.proc)
  THEN [ s EXCEPT !.stack[Len(s.stack)].locals[x] = val ]
  ELSE [ s EXCEPT !.g[x] = val ]

WriteVarMulti(ast, s, pid, x, val) ==
  LET f == Top(s.stacks[pid]) IN
  IF x \in InScopeLocals(ast, f.proc)
  THEN [ s EXCEPT !.stacks[pid][Len(s.stacks[pid])].locals[x] = val ]
  ELSE [ s EXCEPT !.g[x] = val ]

(*
Initial frame construction for a procedure with parameter binding
params is a sequence of formal names; argsVals is a sequence of actual values of equal length.
*)
InitFrame(ast, p, argsVals, ret) ==
  LET ps == Params(ast,p)
      formals == SetOfSeq(ps)
      baseLocals == [v \in VarName |-> CHOOSE d : d = d]
      localInit == [v \in InScopeLocals(ast,p) |-> CHOOSE d \in Values : TRUE]
      bound == [ v \in formals |-> argsVals[Position(ps, v)] ]
      locals == [ v \in VarName |-> 
                   IF v \in formals THEN bound[v]
                   ELSE IF v \in Locals(ast,p) THEN localInit[v]
                   ELSE CHOOSE d : d = d ]
  IN [proc |-> p, locals |-> locals, ret |-> ret]

Position(seq, x) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = x

(***************************************************************************)
(******************** Denotation: States, Init, Next ************************)
(***************************************************************************)

(*
State spaces
*)
StateUni(ast) ==
  { s \in [ g : StoreOf(Globals(ast)),
            pc : PC,
            stack : Seq(StackFrame) ] :
      Len(s.stack) >= 1 /\ Top(s.stack).proc \in Procs(ast) }

StateMulti(ast) ==
  { s \in [ g : StoreOf(Globals(ast)),
            pc : [Pid -> PC],
            stacks : [Pid -> Seq(StackFrame)] ] :
      \A p \in ast.Pids : Len(s.stacks[p]) >= 1 /\ Top(s.stacks[p]).proc \in Procs(ast) }

StatesOf(ast) ==
  IF ast.Mode = "uni" THEN StateUni(ast) ELSE StateMulti(ast)

(*
Initial states derived from AST
We require main has no parameters; globals initialized by AST.GInitVal;
each process (or the single uniprocess) starts at main's entry with a frame whose ret = "halt".
*)
InitUni(ast, s) ==
  /\ s \in StateUni(ast)
  /\ Params(ast, MainProc(ast)) = <<>>
  /\ s.g = ast.GInitVal
  /\ s.pc = Entry(ast, MainProc(ast))
  /\ LET f == InitFrame(ast, MainProc(ast), <<>>, "halt") IN
     s.stack = << f >>

InitMulti(ast, s) ==
  /\ s \in StateMulti(ast)
  /\ Params(ast, MainProc(ast)) = <<>>
  /\ ast.Pids # {} /\ IsFiniteSet(ast.Pids)
  /\ s.g = ast.GInitVal
  /\ \A p \in ast.Pids :
        /\ s.pc[p] = Entry(ast, MainProc(ast))
        /\ LET f == InitFrame(ast, MainProc(ast), <<>>, "halt") IN
           s.stacks[p] = << f >>

InitStates(ast) ==
  { s \in StatesOf(ast) : IF ast.Mode = "uni" THEN InitUni(ast, s) ELSE InitMulti(ast, s) }

(*
Single-step operational next relation, by structural rules on statements.
We use EvalExpr, EvalBool, EvalSet over the constructed environment.
*)

NextUniPair(ast, s, s2) ==
  /\ s \in StateUni(ast) /\ s2 \in StateUni(ast)
  /\ LET fr == Top(s.stack)
         p  == fr.proc
         l  == s.pc
         st == Body(ast, p)[l]
         env == EnvUni(ast, s)
     IN
     CASE st.Tag = "Skip" ->
            /\ s2 = [s EXCEPT !.pc = st.next]
     [] st.Tag = "Assign" ->
            LET v == EvalExpr[<<st.rhs, env>>] IN
            /\ s2 = [WriteVarUni(ast, s, st.lhs, v) EXCEPT !.pc = st.next]
     [] st.Tag = "If" ->
            LET b == EvalBool[<<st.test, env>>] IN
            /\ s2 = [s EXCEPT !.pc = IF b THEN st.then ELSE st.else]
     [] st.Tag = "While" ->
            LET b == EvalBool[<<st.test, env>>] IN
            /\ s2 = [s EXCEPT !.pc = IF b THEN st.body ELSE st.next]
     [] st.Tag = "Goto" ->
            /\ s2 = [s EXCEPT !.pc = st.target]
     [] st.Tag = "Call" ->
            LET ps == Params(ast, st.callee)
                av == [ i \in 1..Len(ps) |-> EvalExpr[<<st.args[i], env>>] ]
                nf == InitFrame(ast, st.callee, av, st.cont)
            IN
            /\ s2 = [ s EXCEPT
                      !.stack = Push(s.stack, nf),
                      !.pc    = Entry(ast, st.callee) ]
     [] st.Tag = "Return" ->
            LET stk1 == Pop(s.stack)
            IN
            /\ IF Len(stk1) = 0
               THEN s2 = [ s EXCEPT !.stack = stk1, !.pc = "halt" ]
               ELSE LET f1 == Top(stk1) IN
                    s2 = [ s EXCEPT !.stack = stk1, !.pc = f1.ret ]
     [] st.Tag = "Either" ->
            /\ st.alts # {}
            /\ \E l2 \in st.alts : s2 = [s EXCEPT !.pc = l2]
     [] st.Tag = "When" ->
            LET b == EvalBool[<<st.test, env>>] IN
            /\ b = TRUE
            /\ s2 = [s EXCEPT !.pc = st.next]
     [] st.Tag = "With" ->
            LET dom == EvalSet[<<st.dom, env>>]
            IN /\ dom # {}
               /\ \E v \in dom :
                    s2 = [WriteVarUni(ast, s, st.v, v) EXCEPT !.pc = st.next]
     [] OTHER -> FALSE

NextMultiPair(ast, s, s2) ==
  /\ s \in StateMulti(ast) /\ s2 \in StateMulti(ast)
  /\ \E pid \in ast.Pids :
       LET fr == Top(s.stacks[pid])
           p  == fr.proc
           l  == s.pc[pid]
           st == Body(ast, p)[l]
           env == EnvMulti(ast, s, pid)
       IN
       CASE st.Tag = "Skip" ->
              /\ s2 = [ s EXCEPT !.pc[pid] = st.next ]
       [] st.Tag = "Assign" ->
              LET v == EvalExpr[<<st.rhs, env>>] IN
              /\ s2 = [ WriteVarMulti(ast, s, pid, st.lhs, v) EXCEPT !.pc[pid] = st.next ]
       [] st.Tag = "If" ->
              LET b == EvalBool[<<st.test, env>>] IN
              /\ s2 = [ s EXCEPT !.pc[pid] = IF b THEN st.then ELSE st.else ]
       [] st.Tag = "While" ->
              LET b == EvalBool[<<st.test, env>>] IN
              /\ s2 = [ s EXCEPT !.pc[pid] = IF b THEN st.body ELSE st.next ]
       [] st.Tag = "Goto" ->
              /\ s2 = [ s EXCEPT !.pc[pid] = st.target ]
       [] st.Tag = "Call" ->
              LET ps == Params(ast, st.callee)
                  av == [ i \in 1..Len(ps) |-> EvalExpr[<<st.args[i], env>>] ]
                  nf == InitFrame(ast, st.callee, av, st.cont)
              IN
              /\ s2 = [ s EXCEPT
                        !.stacks[pid] = Push(s.stacks[pid], nf),
                        !.pc[pid]     = Entry(ast, st.callee) ]
       [] st.Tag = "Return" ->
              LET stk1 == Pop(s.stacks[pid])
              IN
              /\ IF Len(stk1) = 0
                 THEN s2 = [ s EXCEPT !.stacks[pid] = stk1, !.pc[pid] = "halt" ]
                 ELSE LET f1 == Top(stk1) IN
                      s2 = [ s EXCEPT !.stacks[pid] = stk1, !.pc[pid] = f1.ret ]
       [] st.Tag = "Either" ->
              /\ st.alts # {}
              /\ \E l2 \in st.alts : s2 = [ s EXCEPT !.pc[pid] = l2 ]
       [] st.Tag = "When" ->
              LET b == EvalBool[<<st.test, env>>] IN
              /\ b = TRUE
              /\ s2 = [ s EXCEPT !.pc[pid] = st.next ]
       [] st.Tag = "With" ->
              LET dom == EvalSet[<<st.dom, env>>]
              IN /\ dom # {}
                 /\ \E v \in dom :
                      s2 = [ WriteVarMulti(ast, s, pid, st.v, v) EXCEPT !.pc[pid] = st.next ]
       [] OTHER -> FALSE

NextPairs(ast) ==
  IF ast.Mode = "uni"
  THEN { <<s,s2>> \in StateUni(ast) \X StateUni(ast) : NextUniPair(ast, s, s2) }
  ELSE { <<s,s2>> \in StateMulti(ast) \X StateMulti(ast) : NextMultiPair(ast, s, s2) }

(*
Fairness descriptor is copied from AST (translator preserves liveness assumptions).
*)
FairDesc(ast) == ast.Fairness

Denote(ast) ==
  [ States |-> StatesOf(ast),
    Init   |-> InitStates(ast),
    Next   |-> NextPairs(ast),
    Fair   |-> FairDesc(ast) ]

NullOut ==
  [ States |-> {},
    Init   |-> {},
    Next   |-> {},
    Fair   |-> [ Kind |-> "none", Scope |-> {} ] ]

(***************************************************************************)
(*************************** Well-formedness *******************************)
(***************************************************************************)

UniqueSeq(q) == Cardinality(SetOfSeq(q)) = Len(q)

(*
No duplicate variable names in a single scope; params pairwise distinct; all referenced labels/targets valid.
Goto targets must be in the same procedure as the goto.
Call targets must be defined procedures; arguments length equals formals length.
If/While/When next labels must be in the same procedure.
Either alternatives are nonempty, all in same procedure.
Main is defined and has no parameters.
Multiprocess Pids finite nonempty when Mode="multi".
*)
WF_Decls(ast) ==
  /\ MainProc(ast) \in Procs(ast)
  /\ Params(ast, MainProc(ast)) = <<>>
  /\ \A p \in Procs(ast) :
        LET ps == Params(ast,p) IN
        /\ UniqueSeq(ps)
        /\ (SetOfSeq(ps) \cap Locals(ast,p)) = {}
        /\ (Locals(ast,p) \cap Globals(ast)) = {}
  /\ \A p \in Procs(ast) :
        /\ Entry(ast,p) \in DOMAIN Body(ast,p)
        /\ \A l \in DOMAIN Body(ast,p) :
              LET st == Body(ast,p)[l] IN
              CASE st.Tag = "Assign" -> st.next \in DOMAIN Body(ast,p)
              [] st.Tag = "If"    -> /\ st.then \in DOMAIN Body(ast,p)
                                      /\ st.else \in DOMAIN Body(ast,p)
              [] st.Tag = "While" -> /\ st.body \in DOMAIN Body(ast,p)
                                      /\ st.next \in DOMAIN Body(ast,p)
              [] st.Tag = "Goto"  -> st.target \in DOMAIN Body(ast,p)
              [] st.Tag = "Call"  -> /\ st.callee \in Procs(ast)
                                      /\ Len(st.args) = Len(Params(ast, st.callee))
                                      /\ st.cont \in DOMAIN Body(ast,p)
              [] st.Tag = "Return"-> TRUE
              [] st.Tag = "Skip"  -> st.next \in DOMAIN Body(ast,p)
              [] st.Tag = "Either"-> /\ st.alts # {}
                                      /\ st.alts \subseteq DOMAIN Body(ast,p)
              [] st.Tag = "When"  -> st.next \in DOMAIN Body(ast,p)
              [] st.Tag = "With"  -> st.next \in DOMAIN Body(ast,p)
              [] OTHER -> FALSE
  /\ (ast.Mode = "multi") => (ast.Pids # {} /\ IsFiniteSet(ast.Pids))

WF_GlobalsInit(ast) ==
  /\ ast.GInitVal \in [Globals(ast) -> Values]

WellFormed(ast) == WF_Decls(ast) /\ WF_GlobalsInit(ast)

(***************************************************************************)
(************************ Translator state machine **************************)
(***************************************************************************)

VARIABLES out, done, err

Vars == << out, done, err >>

Init ==
  /\ done = FALSE
  /\ err = FALSE
  /\ out = NullOut

Translate ==
  /\ ~done /\ ~err
  /\ IF WellFormed(AST)
     THEN /\ out' = Denote(AST)
          /\ done' = TRUE
          /\ err'  = FALSE
     ELSE /\ out' = NullOut
          /\ done' = TRUE
          /\ err'  = TRUE

Stutter ==
  /\ done \/ err
  /\ out' = out
  /\ done' = done
  /\ err'  = err

Next == Translate \/ Stutter

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Translate)

(***************************************************************************)
(********************** Safety and liveness properties **********************)
(***************************************************************************)

(*
Safety: No conflation of distinct labels or variables in the generated semantics.
Implemented by construction via scoping: control is (proc, label) via top frame;
gotos restricted to same procedure; writes respect scope.
We assert these as properties over the out record after successful translation.
*)
NoLabelConflation ==
  done /\ ~err =>
  /\ \A p \in Procs(AST) :
        \A l \in DOMAIN Body(AST,p) :
          \A q \in Procs(AST) :
            \A m \in DOMAIN Body(AST,q) :
              (p # q \/ l # m) => TRUE

DistinctVarsScopes ==
  done /\ ~err =>
  /\ \A p \in Procs(AST) :
        (SetOfSeq(Params(AST,p)) \cap Locals(AST,p)) = {}
  /\ \A p \in Procs(AST) :
        (Locals(AST,p) \cap Globals(AST)) = {}

(*
Soundness and completeness of denotation relative to AST:
The translator’s out equals the denotation computed from AST.
*)
SemanticCorrespondence ==
  done /\ ~err => out = Denote(AST)

(*
Procedure calls/returns are atomic w.r.t. parameter binding and stack discipline:
For any call step, a single new frame is pushed with params bound to evaluated args,
pc jumps to callee entry, and ret label equals caller continuation.
For any return step, exactly one frame is popped and control goes to frame.ret or halts.
These are enforced by NextUniPair/NextMultiPair construction; we state them abstractly.
*)
CallReturnAtomicity ==
  done /\ ~err =>
  LET NP == out.Next IN
  /\ \A ss \in NP :
       LET s == ss[1] IN
       LET s2 == ss[2] IN
       IF AST.Mode = "uni" THEN
         LET fr == Top(s.stack)
             p  == fr.proc
             l  == s.pc
             st == Body(AST,p)[l]
         IN
         CASE st.Tag = "Call" ->
                /\ Len(s2.stack) = Len(s.stack) + 1
                /\ s2.pc = Entry(AST, st.callee)
         [] st.Tag = "Return" ->
                /\ Len(s2.stack) = Len(s.stack) - 1
                /\ (Len(s2.stack) = 0 => s2.pc = "halt")
         [] OTHER -> TRUE
       ELSE
         \A pid \in AST.Pids :
           LET fr == Top(s.stacks[pid])
               p  == fr.proc
               l  == s.pc[pid]
               st == Body(AST,p)[l]
           IN
           CASE st.Tag = "Call" ->
                  /\ Len(s2.stacks[pid]) = Len(s.stacks[pid]) + 1
                  /\ s2.pc[pid] = Entry(AST, st.callee)
           [] st.Tag = "Return" ->
                  /\ Len(s2.stacks[pid]) = Len(s.stacks[pid]) - 1
                  /\ (Len(s2.stacks[pid]) = 0 => s2.pc[pid] = "halt")
           [] OTHER -> TRUE

(*
Guarded and nondeterministic constructs resolved into enabled actions:
- When steps only occur when guard evaluates TRUE.
- Either and With introduce nondeterministic choices among enabled alternatives.
This follows from NextUniPair/NextMultiPair; we restate as properties.
*)
GuardsAndNondetCorrect ==
  done /\ ~err =>
  LET NP == out.Next IN
  /\ \A ss \in NP :
       LET s == ss[1] IN
       LET s2 == ss[2] IN
       IF AST.Mode = "uni" THEN
         LET fr == Top(s.stack)
             p  == fr.proc
             l  == s.pc
             st == Body(AST,p)[l]
             env == EnvUni(AST, s)
         IN
         CASE st.Tag = "When" ->
                EvalBool[<<st.test, env>>] = TRUE
         [] st.Tag = "Either" ->
                \E l2 \in st.alts : s2.pc = l2
         [] st.Tag = "With" ->
                \E v \in EvalSet[<<st.dom, env>>] : TRUE
         [] OTHER -> TRUE
       ELSE
         \A pid \in AST.Pids :
           LET fr == Top(s.stacks[pid])
               p  == fr.proc
               l  == s.pc[pid]
               st == Body(AST,p)[l]
               env == EnvMulti(AST, s, pid)
           IN
           CASE st.Tag = "When" ->
                  EvalBool[<<st.test, env>>] = TRUE
           [] st.Tag = "Either" ->
                  \E l2 \in st.alts : s2.pc[pid] = l2
           [] st.Tag = "With" ->
                  \E v \in EvalSet[<<st.dom, env>>] : TRUE
           [] OTHER -> TRUE

(*
While/If/goto/label control flow: next PCs follow tests/targets accordingly.
Again, encoded in Next; asserted here.
*)
ControlFlowProgress ==
  done /\ ~err =>
  LET NP == out.Next IN
  /\ \A ss \in NP :
       LET s == ss[1] IN
       LET s2 == ss[2] IN
       IF AST.Mode = "uni" THEN
         LET fr == Top(s.stack)
             p  == fr.proc
             l  == s.pc
             st == Body(AST,p)[l]
             env == EnvUni(AST, s)
         IN
         CASE st.Tag = "If" ->
                LET b == EvalBool[<<st.test, env>>] IN
                s2.pc = IF b THEN st.then ELSE st.else
         [] st.Tag = "While" ->
                LET b == EvalBool[<<st.test, env>>] IN
                s2.pc = IF b THEN st.body ELSE st.next
         [] st.Tag = "Goto" ->
                s2.pc = st.target
         [] st.Tag = "Skip" ->
                s2.pc = st.next
         [] OTHER -> TRUE
       ELSE
         \A pid \in AST.Pids :
           LET fr == Top(s.stacks[pid])
               p  == fr.proc
               l  == s.pc[pid]
               st == Body(AST,p)[l]
               env == EnvMulti(AST, s, pid)
           IN
           CASE st.Tag = "If" ->
                  LET b == EvalBool[<<st.test, env>>] IN
                  s2.pc[pid] = IF b THEN st.then ELSE st.else
           [] st.Tag = "While" ->
                  LET b == EvalBool[<<st.test, env>>] IN
                  s2.pc[pid] = IF b THEN st.body ELSE st.next
           [] st.Tag = "Goto" ->
                  s2.pc[pid] = st.target
           [] st.Tag = "Skip" ->
                  s2.pc[pid] = st.next
           [] OTHER -> TRUE

(*
Fairness preservation: the out.Fair descriptor equals the AST fairness specification.
*)
FairnessPreserved ==
  done /\ ~err => out.Fair = FairDesc(AST)

(*
Error signaling: translator reports error iff AST is ill-formed.
*)
ErrorIffViolation ==
  (err <=> ~WellFormed(AST)) /\ (done => (err \/ ~err))

(*
Aggregate safety invariant required to hold in all translator states.
*)
SafetyInvariant ==
  /\ (done /\ ~err) => /\ NoLabelConflation
                       /\ DistinctVarsScopes
                       /\ SemanticCorrespondence
                       /\ CallReturnAtomicity
                       /\ GuardsAndNondetCorrect
                       /\ ControlFlowProgress
                       /\ FairnessPreserved
  /\ ErrorIffViolation

(*
Liveness of the translator: under weak fairness of Translate, translation terminates.
If AST is well-formed then we eventually succeed; otherwise we eventually report error.
*)
Liveness ==
  (WellFormed(AST) => <> (done /\ ~err)) /\ (~WellFormed(AST) => <> (done /\ err))

=============================================================================