------------------------------ MODULE Translator ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS ProcNames, VarNames, ProcDefs, GlobalDecls, LocalDecls,
          Initializers, Expr, EvalExpr

VARIABLE srcState, tgtState, pc, stack, errorFlag

(* Helper: Get current statement of a procedure *)
GetStmt(procBody, idx) == IF idx <= Len(procBody) THEN procBody[idx] ELSE [type |-> "final"]

Init ==
  /\ errorFlag = FALSE
  /\ srcState = [v \in VarNames |-> Initializers[v]]
  /\ tgtState = srcState
  /\ pc = [p \in ProcNames |-> 1]
  /\ stack = [p \in ProcNames |-> <<>>]

(* Transition for assignment *)
AssignStep(p, stmt) ==
  LET var == stmt.target IN
    /\ tgtState' = [tgtState EXCEPT ![var] = EvalExpr(stmt.expr, tgtState)]
    /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]
    /\ srcState' = srcState
    /\ stack' = stack
    /\ errorFlag' = errorFlag

(* Transition for if *)
IfStep(p, stmt) ==
  LET condVal == EvalExpr(stmt.cond, tgtState) IN
    IF condVal /= 0 THEN
      /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]
    ELSE
      /\ pc' = [pc EXCEPT ![p] = pc[p] + 2]
    /\ tgtState' = tgtState
    /\ srcState' = srcState
    /\ stack' = stack
    /\ errorFlag' = errorFlag

(* Transition for nondeterministic choice *)
ChoiceStep(p, stmt) ==
  /\ pc' = [pc EXCEPT ![p] = CHOOSE i \in {stmt.thenIdx, stmt.elseIdx} : i]
  /\ tgtState' = tgtState
  /\ srcState' = srcState
  /\ stack' = stack
  /\ errorFlag' = errorFlag

(* Transition for loop *)
LoopStep(p, stmt) ==
  LET condVal == EvalExpr(stmt.cond, tgtState) IN
    IF condVal /= 0 THEN
      /\ pc' = [pc EXCEPT ![p] = stmt.bodyIdx]
    ELSE
      /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]
    /\ tgtState' = tgtState
    /\ srcState' = srcState
    /\ stack' = stack
    /\ errorFlag' = errorFlag

(* Transition for procedure call *)
CallStep(p, stmt) ==
  LET callee == stmt.procName IN
    /\ stack' = [stack EXCEPT ![p] = Append(stack[p], pc[p]+1)]
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ tgtState' = tgtState
    /\ srcState' = srcState
    /\ errorFlag' = errorFlag

(* Transition for return *)
ReturnStep(p) ==
  LET retAddr == Head(stack[p]) IN
    /\ stack' = [stack EXCEPT ![p] = Tail(stack[p])]
    /\ pc' = [pc EXCEPT ![p] = retAddr]
    /\ tgtState' = tgtState
    /\ srcState' = srcState
    /\ errorFlag' = errorFlag

(* Transition for final *)
FinalStep(p) ==
  /\ errorFlag' = TRUE
  /\ tgtState' = tgtState
  /\ srcState' = srcState
  /\ pc' = pc
  /\ stack' = stack

Next ==
  ∃ p \in ProcNames :
    LET curStmt == GetStmt(ProcDefs[p], pc[p]) IN
      CASE curStmt.type = "assign" -> AssignStep(p, curStmt)
       [] curStmt.type = "if"     -> IfStep(p, curStmt)
       [] curStmt.type = "choice" -> ChoiceStep(p, curStmt)
       [] curStmt.type = "loop"   -> LoopStep(p, curStmt)
       [] curStmt.type = "call"   -> CallStep(p, curStmt)
       [] curStmt.type = "return" -> ReturnStep(p)
       [] curStmt.type = "final"  -> FinalStep(p)

Spec == Init /\ [][Next]_<<srcState, tgtState, pc, stack, errorFlag>>

SafetyInvariant == srcState = tgtState

Fairness == WF_vars(Next)

THEOREM Spec => SafetyInvariant
=============================================================================