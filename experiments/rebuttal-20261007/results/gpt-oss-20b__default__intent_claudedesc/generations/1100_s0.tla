MODULE MutualExclusionLock
EXTENDS Naturals, TLC

CONSTANTS Proc

VARIABLES lock, pc

StateNC == "nc"
StateAcq == "acq"
StateCS  == "cs"
StateRel == "rel"

TypeInvariant ==
    /\ lock ∈ {0,1}
    /\ ∀p ∈ Proc : pc[p] ∈ {StateNC, StateAcq, StateCS, StateRel}

MutualExcl ==
    LET inLock(p) == (pc[p] = StateCS \/ pc[p] = StateRel)
        countInLock == Cardinality({ p | inLock(p) })
    IN
        /\ countInLock <= 1
        /\ lock = 1 ⇔ ∃p ∈ Proc : inLock(p)

Init ==
    /\ lock = 0
    /\ pc = [p ∈ Proc |-> StateNC]

Step(p) ==
    LET cur == pc[p] IN
        CASE cur = StateNC ->
                /\ pc' = [pc EXCEPT ![p] = StateAcq]
                /\ lock' = lock
          [] cur = StateAcq /\ lock = 0 ->
                /\ pc' = [pc EXCEPT ![p] = StateCS]
                /\ lock' = 1
          [] cur = StateCS ->
                /\ pc' = [pc EXCEPT ![p] = StateRel]
                /\ lock' = lock
          [] cur = StateRel ->
                /\ pc' = [pc EXCEPT ![p] = StateNC]
                /\ lock' = 0

Next ==
    ∃ p ∈ Proc : Step(p)

Spec == Init /\ [][Next]_<<lock, pc>>

Invariant == TypeInvariant /\ MutualExcl
