--------------------------- MODULE TwoProcessMutex ---------------------------
EXTENDS Naturals, TLC

VARIABLES loc, lock

LocSet == {"nc", "l1", "cs"}

Init ==
  /\ loc[1] = "nc"
  /\ loc[2] = "nc"
  /\ lock = 0

MoveToWaiting(i) ==
  /\ i \in {1,2}
  /\ loc[i] = "nc"
  /\ loc' = [loc EXCEPT ![i] = "l1"]
  /\ UNCHANGED <<lock>>

Acquire(i) ==
  /\ i \in {1,2}
  /\ loc[i] = "l1"
  /\ lock = 0
  /\ loc' = [loc EXCEPT ![i] = "cs"]
  /\ lock' = i

Release(i) ==
  /\ i \in {1,2}
  /\ loc[i] = "cs"
  /\ lock' = 0
  /\ loc' = [loc EXCEPT ![i] = "nc"]

Next ==
  \/ ∃ i \in {1,2} : MoveToWaiting(i)
  \/ ∃ i \in {1,2} : Acquire(i)
  \/ ∃ i \in {1,2} : Release(i)

TypeInv ==
  /\ loc \in [1..2 -> LocSet]
  /\ lock \in {0,1,2}

MutualExcl ==
  ~((loc[1] = "cs") /\ (loc[2] = "cs"))

Safety == TypeInv /\ MutualExcl

Liveness ==
  [] ((loc[1] = "l1") -> <> (loc[1] = "cs"))

Spec == Init /\ [][Next]_<<loc, lock>> /\ Safety
=============================================================================