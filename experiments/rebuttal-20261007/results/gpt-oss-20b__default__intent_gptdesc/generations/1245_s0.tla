MODULE Translator
EXTENDS Naturals, Sequences, TLC

CONSTANTS ProcNames, Labels, VarNames, Processes,
          initVal, EvalExpr, EvalBool,
          AST, LabelToStmt, NextLabel,
          FairnessMode, Value, Expr, BoolExpr

ASSUME
    /\ FairnessMode \in {"None", "Weak", "Strong"}
    /\ initVal \in [VarNames -> Value]
    /\ EvalExpr \in [Expr -> Value]
    /\ EvalBool \in [BoolExpr -> BOOLEAN]
    /\ AST \in [ProcNames -> ProcedureBody]
    /\ LabelToStmt \in [Labels -> Statement]
    /\ NextLabel \in [Labels -> Labels]

VARIABLES globalVars, stacks, pc, error

(* Frame record *)
Frame == [proc |-> ProcName,
          locals |-> [VarName -> Value],
          retLbl |-> Label]

Init ==
    /\ globalVars = [v \in VarNames |-> initVal(v)]
    /\ stacks = [p \in Processes |-> <<>>]
    /\ pc = [p \in Processes |-> AST["main"].startLabel]
    /\ error = FALSE

(* Helper actions for each statement type *)
AssignAction(p, s) ==
    LET l == pc[p]
        newVars == [globalVars EXCEPT ![s.var] = EvalExpr(s.expr)] IN
    /\ globalVars' = newVars
    /\ pc'[p] = NextLabel[l]
    /\ UNCHANGED <<stacks, error>>

IfAction(p, s) ==
    LET l == pc[p] IN
    /\ IF EvalBool(s.guard) THEN
        /\ pc'[p] = s.thenLbl
       ELSE
        /\ pc'[p] = s.elseLbl
    /\ UNCHANGED <<globalVars, stacks, error>>

WhileAction(p, s) ==
    LET l == pc[p] IN
    /\ IF EvalBool(s.guard) THEN
        /\ pc'[p] = s.bodyLbl
       ELSE
        /\ pc'[p] = NextLabel[l]
    /\ UNCHANGED <<globalVars, stacks, error>>

CallAction(p, s) ==
    LET l == pc[p]
        frame == [proc |-> s.proc,
                  locals |-> [v \in VarNames |-> initVal(v)],
                  retLbl |-> NextLabel[l]] IN
    /\ stacks'[p] = Append(stacks[p], frame)
    /\ pc'[p] = AST[s.proc].startLabel
    /\ UNCHANGED <<globalVars, error>>

ReturnAction(p) ==
    LET stack == stacks[p]
        lastFrame == Last(stack)
        newStack == SubSeq(stack, 1, Len(stack)-1) IN
    /\ Len(stack) > 0
    /\ stacks'[p] = newStack
    /\ pc'[p] = lastFrame.retLbl
    /\ UNCHANGED <<globalVars, error>>

GotoAction(p, s) ==
    LET l == pc[p] IN
    /\ pc'[p] = s.target
    /\ UNCHANGED <<globalVars, stacks, error>>

EitherAction(p, s) ==
    LET l == pc[p]
        i == CHOOSE i \in 1..Len(s.guards) : EvalBool(s.guards[i]) IN
    /\ Len(s.guards) > 0
    /\ pc'[p] = s.targets[i]
    /\ UNCHANGED <<globalVars, stacks, error>>

ChoiceAction(p, s) ==
    LET l == pc[p]
        opt == CHOOSE o \in s.options : TRUE IN
    /\ ActionForStmt(p, opt)

(* Dispatch for a single statement *)
ActionForStmt(p, s) ==
    CASE s.type = "assign" -> AssignAction(p, s)
         [] s.type = "if"   -> IfAction(p, s)
         [] s.type = "while"-> WhileAction(p, s)
         [] s.type = "call" -> CallAction(p, s)
         [] s.type = "return"-> ReturnAction(p)
         [] s.type = "goto" -> GotoAction(p, s)
         [] s.type = "either"-> EitherAction(p, s)
         [] s.type = "choice"-> ChoiceAction(p, s)

Next ==
    \E p \in Processes :
        LET l == pc[p]
            s == LabelToStmt[l] IN
        ActionForStmt(p, s)

Spec ==
    Init /\ [][Next]_<<globalVars, stacks, pc, error>>

Fairness ==
    IF FairnessMode = "Weak" THEN WEAK FAIRNESS (Next)
    ELSE IF FairnessMode = "Strong" THEN STRONG FAIRNESS (Next)
    ELSE \TRUE

SpecWithFairness == Spec /\ Fairness

(* Invariants *)
NoDuplicateLabels ==
    \A l1, l2 \in Labels : l1 # l2 => LabelToStmt[l1] != LabelToStmt[l2]

Invariant1 ==
    \A p \in Processes : pc[p] \in Labels

THEOREM Correctness ==
    SpecWithFairness => Invariant1

END MODULE