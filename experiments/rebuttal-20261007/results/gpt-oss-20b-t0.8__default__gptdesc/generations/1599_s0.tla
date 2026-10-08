MODULE FastMutex
EXTENDS Naturals

CONSTANTS N

VARIABLES x, y, b, pc

(* Variable type invariants *)
xType == (0 <= x /\ x <= N) \/ x = 0
yType == (0 <= y /\ y <= N) \/ y = 0
bType == b \in [1..N -> BOOLEAN]
pcType == pc \in [1..N -> {"Noncritical", "Entry", "Critical", "Exit"}]

Init ==
   /\ x = 0
   /\ y = 0
   /\ b = [i \in 1..N |-> FALSE]
   /\ pc = [i \in 1..N |-> "Noncritical"]
   /\ xType
   /\ yType
   /\ bType
   /\ pcType

(* Actions *)
NoncriticalToEntry(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Noncritical"
   /\ pc' = [pc EXCEPT ![i] = "Entry"]
   /\ b' = [b EXCEPT ![i] = TRUE]
   /\ x' = i
   /\ y' = y

EntryToCritical(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Entry"
   /\ pc' = [pc EXCEPT ![i] = "Critical"]
   /\ UNCHANGED <<x, y, b>>

CriticalToExit(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Critical"
   /\ pc' = [pc EXCEPT ![i] = "Exit"]
   /\ UNCHANGED <<x, y, b>>

ExitToNoncritical(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Exit"
   /\ pc' = [pc EXCEPT ![i] = "Noncritical"]
   /\ b' = [b EXCEPT ![i] = FALSE]
   /\ UNCHANGED <<x, y>>

SkipNoncritical(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Noncritical"
   /\ pc' = pc
   /\ UNCHANGED <<x, y, b>>

SkipCritical(i) ==
   /\ i \in 1..N
   /\ pc[i] = "Critical"
   /\ pc' = pc
   /\ UNCHANGED <<x, y, b>>

Next ==
   \/ \E i \in 1..N : NoncriticalToEntry(i)
   \/ \E i \in 1..N : EntryToCritical(i)
   \/ \E i \in 1..N : CriticalToExit(i)
   \/ \E i \in 1..N : ExitToNoncritical(i)
   \/ \E i \in 1..N : SkipNoncritical(i)
   \/ \E i \in 1..N : SkipCritical(i)

(* Fair actions (exclude skip steps) *)
FairAction ==
   \E i \in 1..N :
      NoncriticalToEntry(i) \/ EntryToCritical(i) \/ CriticalToExit(i) \/ ExitToNoncritical(i)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars[FairAction]

(* Safety invariant: at most one process in critical section *)
InCS(i) == pc[i] = "Critical"

NoTwoInCS ==
   \A i, j \in 1..N :
      (i /= j => ~(InCS(i) /\ InCS(j)))

SafetySpec == FairSpec /\ NoTwoInCS

(* Liveness: every process eventually enters critical section *)
Liveness_i(i) == []<>(pc[i] = "Critical")

Liveness == \A i \in 1..N : Liveness_i(i)

(* Conditional liveness: if in Entry, eventually Critical *)
CondLiveness_i(i) ==
   [](pc[i] = "Entry" => <> (pc[i] = "Critical"))

CondLiveness == \A i \in 1..N : CondLiveness_i(i)

FullSpec == SafetySpec /\ Liveness /\ CondLiveness

=============================================================================