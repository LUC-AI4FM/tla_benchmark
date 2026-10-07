------------------------------ MODULE PlusCalTranslation ------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  This module models the translation from a (global-naming) PlusCal abstract syntax tree
  to its corresponding TLA+ specification. It defines:
  - A grammar for a flattened, label-directed control graph form of a PlusCal program
    (post explosion of structured statements and translation of calls/returns/gotos).
  - A translation pipeline interface (as operators) that can be instantiated as identity
    on already-flattened inputs.
  - A TLA+ semantics with process-local subscripts, type/safety invariants,
    configurable fairness, and a Termination liveness property.

  Notes and limitations (executable under TLC):
  - Expressions in assignments are modeled as constant values (stmt.val ∈ Val),
    not as arbitrary state-dependent expressions.
  - The translation pipeline operators are declarative; in TLC runs, supply Program
    that already satisfies IsFlatProgram and consider the pipeline identity.
  - Errors (e.g., ill-typed targets) are ruled out by IsFlatProgram constraints.
  - Owner mapping binds each label to exactly one process (global naming).
*)

CONSTANTS
  P,          \* Set of process identifiers
  Labels,     \* Set of labels
  Vars,       \* Set of variable names (global naming)
  Val,        \* Set of storable values
  Null,       \* Distinguished null marker (not in P, Labels, Vars, Val)
  FairnessOption, \* One of {"None","WFProc","WFNext","SFProc"}
  Program     \* The flattened, translated program (see IsFlatProgram)

(*
  Statement kinds supported in the flattened program:
    - "Assign": write a constant value to a target variable, then goto 'to'
    - "Goto": jump to 'to'
    - "Skip": no state change, goto 'to'
    - "End": terminate the owning process (pc := "Done")
  Any structured constructs (If/While/Call/Return/Block) are assumed to have been
  exploded/translated to this form in earlier pipeline stages.
*)
StmtKinds == {"Assign","Goto","Skip","End"}

(*
  Grammar and well-formedness for a flattened program.
  A Program is a record with fields:
    - globals \subseteq Vars
    - locals \in [P -> SUBSET Vars]   (process-local names; disjoint from globals)
    - owners \in [Labels -> P]        (label ownership; global naming)
    - entry  \in [P -> Labels]        (per-process entry labels)
    - stmts  \in [Labels -> [ kind: StmtKinds,
                               target: Vars \cup {Null},
                               val: Val \cup {Null},
                               to: Labels \cup {Null} ]]
    - init   \in [ g: [globals -> Val],
                   l: [p \in P |-> [locals[p] -> Val]] ]
  Additional constraints tie fields together and rule out malformed graphs.
*)
IsFlatProgram(Prog) ==
  LET G == Prog.globals
      L == Prog.locals
      OWN == Prog.owners
      E == Prog.entry
      S == Prog.stmts
      I == Prog.init
      AllLocals == UNION { L[p] : p \in P }
  IN /\ G \subseteq Vars
     /\ L \in [P -> SUBSET Vars]
     /\ G \cap AllLocals = {}
     /\ OWN \in [Labels -> P]
     /\ E \in [P -> Labels]
     /\ \A p \in P : OWN[E[p]] = p
     /\ S \in [Labels -> [ kind: StmtKinds,
                           target: Vars \cup {Null},
                           val: Val \cup {Null},
                           to: Labels \cup {Null} ]]
     /\ \A lab \in DOMAIN S :
          LET s == S[lab] IN
            IF s.kind = "Assign" THEN
              /\ s.target \in Vars
              /\ s.val \in Val
              /\ s.to \in Labels
            ELSE IF s.kind = "Goto" THEN
              /\ s.target = Null
              /\ s.val = Null
              /\ s.to \in Labels
            ELSE IF s.kind = "Skip" THEN
              /\ s.target = Null
              /\ s.val = Null
              /\ s.to \in Labels
            ELSE \* "End"
              /\ s.kind = "End"
              /\ s.target = Null
              /\ s.val = Null
              /\ s.to = Null
     /\ \A lab \in DOMAIN S :
          LET s == S[lab] IN
            /\ OWN[lab] \in P
            /\ IF s.kind \in {"Assign","Goto","Skip"} THEN s.to \in DOMAIN S ELSE TRUE
     /\ I \in [ g: [G -> Val],
                l: [p \in P |-> [L[p] -> Val]] ]

(*
  Translation pipeline interface:
   - ExplodeStructured: explode structured, labeled statements into flat ones
   - TranslateCallsReturnsGotos: resolve calls/returns/gotos to explicit control edges
   - AddSubscriptsForLocals: add process subscripts for process-local variables
  These are modeled as pure operators on ASTs. In typical TLC use, supply Program
  that already satisfies IsFlatProgram, and view the composite as identity.
*)
ExplodeStructured(ast) == ast
TranslateCallsReturnsGotos(ast) == ast
AddSubscriptsForLocals(ast) == ast
Pipeline(ast) == AddSubscriptsForLocals(TranslateCallsReturnsGotos(ExplodeStructured(ast)))

ASSUME
  /\ FairnessOption \in {"None","WFProc","WFNext","SFProc"}
  /\ Null \notin (P \cup Labels \cup Vars \cup Val)
  /\ "Done" \notin Labels
  /\ IsFlatProgram(Program)

(*
  State variables:
    - g: store for globals
    - l: per-process store for locals
    - pc: per-process program counter (labels or "Done")
*)
VARIABLES g, l, pc

vars == << g, l, pc >>

GlobalVars == Program.globals
LocalVars(p) == Program.locals[p]
Owner(lab) == Program.owners[lab]
Stmt(lab) == Program.stmts[lab]

AllLabels == DOMAIN Program.stmts

(*
  Typing and structural invariant over states.
*)
TypeOK ==
  /\ g \in [GlobalVars -> Val]
  /\ l \in [p \in P |-> [LocalVars(p) -> Val]]
  /\ pc \in [P -> (AllLabels \cup {"Done"})]
  /\ \A p \in P :
        IF pc[p] \in AllLabels THEN Owner(pc[p]) = p ELSE pc[p] = "Done"

(*
  Initial condition: initialize pc to per-process entries, and stores from Program.init.
*)
Init ==
  /\ pc = [p \in P |-> Program.entry[p]]
  /\ g = Program.init.g
  /\ l = Program.init.l
  /\ TypeOK

(*
  Helper to compute the updated local store after an assignment to a local var of p.
*)
UpdateLocalStore(lstore, p, x, v) ==
  IF x \in LocalVars(p)
    THEN [lstore EXCEPT ![p][x] = v]
    ELSE lstore

(*
  Per-process action: a single step by process p according to the statement at pc[p].
  Assign: write constant value to either a global or a local (of p), then goto s.to.
  Goto/Skip: change only pc to s.to.
  End: set pc[p] := "Done".
*)
NextProc(p) ==
  /\ p \in P
  /\ pc[p] \in AllLabels
  /\ LET s == Stmt(pc[p]) IN
       /\ IF s.kind = "Assign" THEN
            /\ g' = IF s.target \in GlobalVars
                      THEN [g EXCEPT ![s.target] = s.val]
                      ELSE g
            /\ l' = UpdateLocalStore(l, p, s.target, s.val)
          ELSE
            /\ g' = g
            /\ l' = l
       /\ pc' = [pc EXCEPT
                   ![p] = IF s.kind = "End" THEN "Done" ELSE s.to]

(*
  System-wide next step: some process takes a step.
*)
Next ==
  \E p \in P : NextProc(p)

(*
  Configurable fairness options:
    - "None"  : no fairness constraints
    - "WFProc": weak fairness on each per-process action
    - "WFNext": weak fairness on the combined Next action
    - "SFProc": strong fairness on each per-process action
*)
Fairness ==
  IF FairnessOption = "None" THEN TRUE
  ELSE IF FairnessOption = "WFProc" THEN
    \A p \in P : WF_vars(NextProc(p))
  ELSE IF FairnessOption = "WFNext" THEN
    WF_vars(Next)
  ELSE IF FairnessOption = "SFProc" THEN
    \A p \in P : SF_vars(NextProc(p))
  ELSE TRUE

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Safety invariants (to be checked under Spec).
*)
Inv_TypeOK == TypeOK

(*
  Termination liveness property: eventually all processes are Done.
  Under appropriate fairness, TLC can be used to check Spec => Termination.
*)
AllDone == \A p \in P : pc[p] = "Done"
Termination == <>AllDone

=============================================================================