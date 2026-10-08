MODULE PlusCalToTLASpec
EXTENDS Integers, Sequences, FiniteSets

CONSTANT ProcessNames, FairnessOption \* {NoFairness, WeakProcess, WeakNext, StrongProcess}

VARIABLES state, ast

(* Grammar definitions *)

Label == [id : ANY]
Expr  == [expr : ANY]
Stmt  == [type : ANY, args : Seq]

IsLabel(s) ==
  /\ s#type = "label"
  /\ s#args #= <<>>

IsCall(st) ==
  /\ st#type = "call"
  /\ st#args /= <<>>

IsStmt(s) == IsLabel(s) \/ IsCall(s)

(* Translation functions *)

Explode(stmt) ==
  IF stmt#type = "label" THEN
      << stmt, [type |-> "goto", args |-> <<stmt#args[1]>>] >>
  ELSE
      << stmt >>

TranslateCalls(stmts) == stmts

AddSubscripts(vars, proc) == vars

(* Build Init *)

BuildInit(ast) ==
  /\ state = [p \in ProcessNames |-> [status |-> "active", local |-> <<>>]]
  /\ ast' = ast

(* Build Next for a process *)

ProcessAction(p) ==
  /\ state[p]#status = "active"
  /\ state' = [state EXCEPT ![p].status = "terminated"]

Next == \E p \in ProcessNames : ProcessAction(p)

NoConflicts(state) == TRUE
SafetyInvariant == NoConflicts(state)
Termination == ALL p \in ProcessNames : state[p]#status = "terminated"

Fairness ==
  IF FairnessOption = WeakProcess THEN
      \E p \in ProcessNames : WEAK_FAIRNESS (ProcessAction(p))
  ELSE
    IF FairnessOption = WeakNext THEN
        WEAK_FAIRNESS Next
    ELSE
      IF FairnessOption = StrongProcess THEN
          STRONG_FAIRNESS (ProcessAction(p))
      ELSE 
          TRUE

Init == BuildInit(ast)

Spec == Init /\ [][Next]_(state,ast) /\ Fairness

Safety := SafetyInvariant
Liveness := Termination

=============================================================================