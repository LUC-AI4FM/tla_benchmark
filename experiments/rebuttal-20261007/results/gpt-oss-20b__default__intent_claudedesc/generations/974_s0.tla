MODULE SharedRegisterAlgorithm
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES shared, local, phase, writing

(* State constants *)
Idle          == 0
WritingStart  == 1
WriteComplete == 2
Done          == 3

(* Type invariant *)
TypeInvariant ==
    /\ shared   ∈ [1..N -> 0 \/ 1]
    /\ local    ∈ [1..N -> 0 \/ 1]
    /\ phase    ∈ [1..N -> {Idle, WritingStart, WriteComplete, Done}]
    /\ writing  ∈ [1..N -> BOOLEAN]

(* Initial state *)
Init ==
    TypeInvariant
    /\ shared   = [i ∈ 1..N |-> 0]
    /\ local    = [i ∈ 1..N |-> 0]
    /\ phase    = [i ∈ 1..N |-> Idle]
    /\ writing  = [i ∈ 1..N |-> FALSE]

(* Actions *)
BeginWrite(i) ==
    /\ i ∈ 1..N
    /\ phase[i] = Idle
    /\ phase'   = [phase EXCEPT ![i] = WritingStart]
    /\ writing' = [writing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<shared, local>>

CompleteWrite(i) ==
    /\ i ∈ 1..N
    /\ phase[i] = WritingStart
    /\ shared'   = [shared EXCEPT ![i] = 1]
    /\ phase'    = [phase EXCEPT ![i] = WriteComplete]
    /\ writing'  = [writing EXCEPT ![i] = FALSE]
    /\ UNCHANGED local

ReadNeighborNonWriting(i) ==
    LET j == IF i > 1 THEN i-1 ELSE N IN
    /\ i ∈ 1..N
    /\ phase[i] = WriteComplete
    /\ ~writing[j]
    /\ local'   = [local EXCEPT ![i] = shared[j]]
    /\ phase'   = [phase EXCEPT ![i] = Done]
    /\ UNCHANGED <<shared, writing>>

ReadNeighborWriting(i) ==
    LET j == IF i > 1 THEN i-1 ELSE N IN
    /\ i ∈ 1..N
    /\ phase[i] = WriteComplete
    /\ writing[j]
    /\ ∃v ∈ {shared[j], 1} : local'   = [local EXCEPT ![i] = v]
    /\ phase'   = [phase EXCEPT ![i] = Done]
    /\ UNCHANGED <<shared, writing>>

Next ==
    ∃i ∈ 1..N :
        BeginWrite(i) \/ CompleteWrite(i) \/ ReadNeighborNonWriting(i) \/ ReadNeighborWriting(i)

(* Invariants *)
PhaseConsistent ==
    ∀i ∈ 1..N : (phase[i] = WritingStart) ⇔ writing[i]

SafetyInvariant ==
    (∀i ∈ 1..N : phase[i] = Done) => (∃i ∈ 1..N : local[i] = 1)

AllDoneLiveness ==
    ∀i ∈ 1..N : □◇(phase[i] = Done)

(* Specification *)
Spec == Init /\ [][Next]_<<shared, local, phase, writing>> /\ PhaseConsistent

THEOREM Safety == Spec => SafetyInvariant
THEOREM Liveness == Spec => AllDoneLiveness
MODULE SharedRegisterAlgorithm END MODULE