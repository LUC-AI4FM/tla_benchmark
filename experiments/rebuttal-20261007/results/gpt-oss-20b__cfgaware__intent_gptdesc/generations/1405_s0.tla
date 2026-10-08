MODULE TwoComponentSystem
IMPORTING Sequences

CONSTANTS NonZero, InitSeq

VARIABLE seq, result

(* Type invariant for all states *)
TypeInvariant ==
    /\ NonZero \in Int
    /\ NonZero # 0
    /\ InitSeq \in Seq(1..100)
    /\ Len(InitSeq) > 0
    /\ result \in Int

(* Initial state *)
Init == 
    /\ seq = InitSeq
    /\ result = 0
    /\ TypeInvariant

(* Inner service is enabled when the result has not yet been updated *)
InnerEnabled == result = 0

(* Atomic action performed by the inner service *)
InnerAction ==
    /\ InnerEnabled
    /\ result' = NonZero
    /\ seq'   = Filter(seq, \lambda x : x # NonZero)

(* Outer controller may stutter when the inner service is disabled *)
OuterStutter ==
    /\ ~InnerEnabled
    /\ seq'   = seq
    /\ result'= result

Next == InnerAction \/ OuterStutter

(* System specification with weak fairness on the inner action *)
Spec == Init /\ [][Next]_vars /\ WF_vars(InnerAction)

(* State in which the system is stable: no further inner actions are enabled *)
StableState ==
    /\ result = NonZero
    /\ seq   = Filter(seq, \lambda x : x # NonZero)

(* Property that eventually the system reaches a stable state and thereafter only stutters *)
SpecRunsToEnd ==
    <> StableState
    /\ [] (StableState => seq' = seq /\ result' = result)

END MODULE