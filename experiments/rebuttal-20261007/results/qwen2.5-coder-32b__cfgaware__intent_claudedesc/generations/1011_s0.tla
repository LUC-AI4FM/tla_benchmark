------------------------------- MODULE KeyValueStore -------------------------------

CONSTANTS Keys, Values

VARIABLES store, currentOp, args, result, processing

(* --algorithm KeyValueStore

variables 
    store = << >>,
    currentOp = "idle",
    args = << >>,
    result = "",
    processing = FALSE;

fair process (P \in 1..3) = begin
    while TRUE do
        with op \in {"get", "insert", "update", "delete"},
             key \in Keys,
             value \in Values do
            either
                /\ currentOp = "idle"
                /\ \/ <<op, key>> \notin {<< "get", k >> : k \in Keys}
                   \/ <<op, key, value>> \notin {<< "insert", k, v >> : k \in Keys, v \in Values}
                   \/ <<op, key, value>> \notin {<< "update", k, v >> : k \in Keys, v \in Values}
                   \/ <<op, key>> \notin {<< "delete", k >> : k \in Keys}
                /\ currentOp' = op
                /\ args' = IF op \in {"get", "delete"} THEN <<key>> ELSE <<key, value>>
                /\ result' = ""
                /\ processing' = TRUE;
            or
                /\ processing
                /\ \/ /\ currentOp = "get"
                       /\ (IF args[1] \notin DOMAIN store THEN result' = "missing" ELSE result' = store[args[1]])
                   \/ /\ currentOp = "insert"
                       /\ (IF args[1] \in DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
                   \/ /\ currentOp = "update"
                       /\ (IF args[1] \notin DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
                   \/ /\ currentOp = "delete"
                      /\ result' = "ok"
                /\ IF currentOp \in {"insert", "update"} THEN
                       IF result' = "ok" THEN store' = (IF currentOp = "insert" THEN <<store EXCEPT ![args[1]] = args[2]>> ELSE <<store EXCEPT ![args[1]] = args[2]>>) 
                   ELSE
                       IF currentOp = "delete" THEN store' = [k \in DOMAIN store \ {args[1]} |-> store[k]]
                   ELSE
                       store' = store
                /\ currentOp' = "idle"
                /\ processing' = FALSE;
end with;

end process

fair process (Q \in 4..6) = begin
    while TRUE do
        await currentOp = "delete";
        await args[1] \notin DOMAIN store;
        await result = "ok";
        await currentOp = "idle";
end with;

end algorithm *)

Spec == /\ Init
        /\ \A P \in 1..3 : SpecProc(P)
        /\ \A Q \in 4..6 : FairDelete(Q)

Init == /\ store = << >>
        /\ currentOp = "idle"
        /\ args = << >>
        /\ result = ""
        /\ processing = FALSE

SpecProc(P) ==
    \/ /\ currentOp = "idle"
       /\ \/ <<currentOp, args[1]>> \notin {<< "get", k >> : k \in Keys}
          \/ <<currentOp, args[1], args[2]>> \notin {<< "insert", k, v >> : k \in Keys, v \in Values}
          \/ <<currentOp, args[1], args[2]>> \notin {<< "update", k, v >> : k \in Keys, v \in Values}
          \/ <<currentOp, args[1]>> \notin {<< "delete", k >> : k \in Keys}
       /\ currentOp' = currentOp
       /\ args' = args
       /\ result' = result
       /\ processing' = TRUE
    \/ /\ processing
       /\ \/ /\ currentOp = "get"
              /\ (IF args[1] \notin DOMAIN store THEN result' = "missing" ELSE result' = store[args[1]])
          \/ /\ currentOp = "insert"
              /\ (IF args[1] \in DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
          \/ /\ currentOp = "update"
              /\ (IF args[1] \notin DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
          \/ /\ currentOp = "delete"
             /\ result' = "ok"
       /\ IF currentOp \in {"insert", "update"} THEN
              IF result' = "ok" THEN store' = (IF currentOp = "insert" THEN <<store EXCEPT ![args[1]] = args[2]>> ELSE <<store EXCEPT ![args[1]] = args[2]>>) 
          ELSE
              IF currentOp = "delete" THEN store' = [k \in DOMAIN store \ {args[1]} |-> store[k]]
          ELSE
              store' = store
       /\ currentOp' = "idle"
       /\ processing' = FALSE

FairDelete(Q) ==
    \E P \in 1..3 :
        WF_<<P>>(\A s, s' \in StateSet : 
            /\ currentOp = "delete" 
            /\ args[1] \notin DOMAIN store
            /\ result = "ok"
            /\ currentOp' = "idle")

TypeOK ==
    /\ store \in [Keys -> Values]
    /\ currentOp \in {"get", "insert", "update", "delete", "idle"}
    /\ args \in {<< >>} \cup {<<k>> : k \in Keys} \cup {<<k, v>> : k \in Keys, v \in Values}
    /\ result \in {"missing", "ok", "error"} \cup Values
    /\ processing \in BOOLEAN

Spec == SpecInit /\ [][Next]_<<store, currentOp, args, result, processing>> /\ TypeOK

SpecInit == Init

Next ==
    \/ /\ currentOp = "idle"
       /\ \/ <<currentOp, args[1]>> \notin {<< "get", k >> : k \in Keys}
          \/ <<currentOp, args[1], args[2]>> \notin {<< "insert", k, v >> : k \in Keys, v \in Values}
          \/ <<currentOp, args[1], args[2]>> \notin {<< "update", k, v >> : k \in Keys, v \in Values}
          \/ <<currentOp, args[1]>> \notin {<< "delete", k >> : k \in Keys}
       /\ currentOp' = currentOp
       /\ args' = args
       /\ result' = result
       /\ processing' = TRUE
    \/ /\ processing
       /\ \/ /\ currentOp = "get"
              /\ (IF args[1] \notin DOMAIN store THEN result' = "missing" ELSE result' = store[args[1]])
          \/ /\ currentOp = "insert"
              /\ (IF args[1] \in DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
          \/ /\ currentOp = "update"
              /\ (IF args[1] \notin DOMAIN store THEN result' = "error" ELSE <<store EXCEPT ![args[1]] = args[2]>>)
          \/ /\ currentOp = "delete"
             /\ result' = "ok"
       /\ IF currentOp \in {"insert", "update"} THEN
              IF result' = "ok" THEN store' = (IF currentOp = "insert" THEN <<store EXCEPT ![args[1]] = args[2]>> ELSE <<store EXCEPT ![args[1]] = args[2]>>) 
          ELSE
              IF currentOp = "delete" THEN store' = [k \in DOMAIN store \ {args[1]} |-> store[k]]
          ELSE
              store' = store
       /\ currentOp' = "idle"
       /\ processing' = FALSE

=============================================================================