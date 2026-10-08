MODULE Barrier

CONSTANT N \in Nat \ {0}

VARIABLES procState, round

Phase == {"AtBarrier", "Arrived", "Released"}

Init ==
  /\ round = 0
  /\ procState = [i \in 1..N |-> "AtBarrier"]

Arrive(i) ==
  /\ i \in 1..N
  /\ procState[i] = "AtBarrier"
  /\ procState' = [procState EXCEPT ![i] = "Arrived"]
  /\ round' = round

ReleaseAll ==
  /\ ALL i \in 1..N : procState[i] = "Arrived"
  /\ procState' = [j \in 1..N |-> "Released"]
  /\ round' = round + 1

Reset(i) ==
  /\ i \in 1..N
  /\ procState[i] = "Released"
  /\ procState' = [procState EXCEPT ![i] = "AtBarrier"]
  /\ round' = round

Next == 
  \/ (\E i \in 1..N : Arrive(i))
  \/ ReleaseAll
  \/ (\E i \in 1..N : Reset(i))

Spec ==
  Init
  /\ [][Next]_<<procState, round>>
  /\ WF_∃(Arrive)
  /\ WF_∃(Reset)
  /\ WF_∃(ReleaseAll)

TypeOK ==
  /\ procState \in [1..N -> Phase]
  /\ round \in Nat

Safety ==
  (\A i, j \in 1..N :
     (procState[i] = "Released" => procState[j] = "Released"))

Liveness ==
  \Box( (\A i \in 1..N : procState[i] = "Arrived")
      => \Diamond(\A i \in 1..N : procState[i] = "Released") )

Reusability ==
  \Box( (\A i \in 1..N : procState[i] = "Released")
      => \Diamond(\A i \in 1..N : procState[i] = "AtBarrier") )

BarrierProperty == TypeOK /\ Safety /\ Liveness /\ Reusability

END MODULE