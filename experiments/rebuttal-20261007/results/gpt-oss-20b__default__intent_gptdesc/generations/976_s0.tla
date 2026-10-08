MODULE RingProcesses
EXTENDS Naturals

CONSTANT N \in Nat

VARIABLES reg, res, state

left(i) == IF i = 1 THEN N ELSE i - 1

AllTerminated == \A i \in 1..N : state[i] = "terminated"

TypeInv ==
    /\ reg \in [1..N -> {0,1}]
    /\ res \in [1..N -> {0,1}]
    /\ state \in [1..N -> {"before","between","terminated"}]

Init ==
    /\ reg = [i \in 1..N |-> 0]
    /\ res = [i \in 1..N |-> 0]
    /\ state = [i \in 1..N |-> "before"]

FirstStep(i) ==
    /\ state[i] = "before"
    /\ reg' = [reg EXCEPT ![i] = 1]
    /\ UNCHANGED <<res, state>>

SecondStep(i) ==
    /\ state[i] = "between"
    /\ res' = [res EXCEPT ![i] = reg[left(i)]]
    /\ state' = [state EXCEPT ![i] = "terminated"]
    /\ UNCHANGED reg

Stutter ==
    /\ AllTerminated
    /\ UNCHANGED <<reg, res, state>>

Next == \/ \E i \in 1..N : FirstStep(i)
      \/ \E i \in 1..N : SecondStep(i)
      \/ Stutter

Spec == Init /\ [][Next]_<<reg, res, state>> /\ Fairness(Next) /\ TypeInv

SafetyProp ==
    [] (AllTerminated => \E i \in 1..N : res[i] = 1)

TerminationLiveness ==
    <> AllTerminated

END MODULE