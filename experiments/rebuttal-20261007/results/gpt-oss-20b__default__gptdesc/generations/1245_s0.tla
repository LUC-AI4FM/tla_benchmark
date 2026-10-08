MODULE PlusCalToTLA
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    ProcessNames,
    FairnessOption,
    InitState,
    NextState,
    UpdateProcVars,
    FinalState,
    InitProcVars,
    AST

VARIABLES
    state,
    procVars

(* Safety invariant placeholder *)
Invariant == TRUE

(* Termination property *)
Termination == <> (state = FinalState)

Init ==
    /\ state   = InitState(AST)
    /\ procVars = [p \in ProcessNames |-> InitProcVars(p)]

Next ==
    LET nextState   == NextState(state, procVars)
        newProcVars == UpdateProcVars(procVars, state)
    IN  /\ state'   = nextState
        /\ procVars'= newProcVars

FairnessCond ==
    CASE FairnessOption = "None"          -> TRUE
         [] FairnessOption = "WeakProcess" -> WF_vars(procVars)
         [] FairnessOption = "WeakNext"    -> WF_next(Next)
         [] FairnessOption = "StrongProcess" -> SF_vars(procVars)

Spec == Init /\ [][Next]_<<state,procVars>> /\ FairnessCond

Safety == Invariant
Liveness == Termination

\* End of module