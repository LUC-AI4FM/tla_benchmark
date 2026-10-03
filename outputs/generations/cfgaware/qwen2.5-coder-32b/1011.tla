------------------------------- MODULE KeyValueStore -------------------------------

CONSTANTS Vals

VARIABLES store, currentOp, argKey, argVal, retValue, ready

(* --algorithm KeyValueStore

variables 
    store = [k \in DOMAIN store |-> MISSING],
    currentOp = "idle",
    argKey = "",
    argVal = "",
    retValue = "",
    ready = TRUE;

defs
    MISSING == CHOOSE x : x \notin Vals;

    Next ==
        \/ /\ ready
           /\ \/ (currentOp = "get" /\ Get)
              \/ (currentOp = "insert" /\ Insert)
              \/ (currentOp = "update" /\ Update)
              \/ (currentOp = "delete" /\ Delete)
        \/ /\ ~ready
           /\ Finish;

    Get ==
        /\ retValue' = store[argKey]
        /\ ready' = TRUE
        /\ currentOp' = "idle";

    Insert ==
        /\ store' = [store EXCEPT ![argKey] = argVal]
        /\ ready' = TRUE
        /\ currentOp' = "idle";

    Update ==
        /\ \/ store[argKey] \in Vals
           /\ store' = [store EXCEPT ![argKey] = argVal]
        /\ ready' = TRUE
        /\ currentOp' = "idle";

    Delete ==
        /\ store' = [store EXCEPT ![argKey] = MISSING]
        /\ ready' = TRUE
        /\ currentOp' = "idle";

    Finish ==
        /\ ready' = FALSE;

Init ==
    /\ store \in [DOMAIN store -> {MISSING} \cup Vals]
    /\ currentOp = "idle"
    /\ argKey \in DOMAIN store
    /\ argVal \in {MISSING} \cup Vals
    /\ retValue \in {MISSING} \cup Vals
    /\ ready = TRUE;

Spec ==
    Init /\ [][Next]_<<store, currentOp, argKey, argVal, retValue, ready>> /\ WF_<<op>>(Delete)

end algorithm *)
=============================================================================