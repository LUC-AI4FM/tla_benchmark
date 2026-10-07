----------------------------- MODULE DijkstraTokenRing -----------------------------

EXTENDS Naturals

CONSTANTS N, K

ASSUME N \in Nat /\ N > 0 /\ K \in Nat /\ K > N

VARIABLES M, pc

Proc == 0..(N - 1)

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

Inc(x) == IF x = K - 1 THEN 0 ELSE x + 1

Guard(i) ==
  IF i = 0 THEN M[0] = M[Left(0)] ELSE M[i] /= M[Left(i)]

NextValue(i) ==
  IF i = 0 THEN Inc(M[0]) ELSE M[Left(i)]

IsHolder(i) == Guard(i)

TokenHolders == { i \in Proc : IsHolder(i) }

SomeoneHoldsToken == \E i \in Proc : IsHolder(i)

SingleToken ==
  \E i \in Proc :
    IsHolder(i)
    /\ \A j \in Proc : j /= i => ~IsHolder(j)

EventuallyJustOneHoldsToken == <>[]SingleToken

Init ==
  /\ M \in [Proc -> 0..(K - 1)]
  /\ pc = [ i \in Proc |-> "try" ]

Check(i) ==
  /\ i \in Proc
  /\ pc[i] = "try"
  /\ Guard(i)
  /\ pc' = [pc EXCEPT ![i] = "act"]
  /\ UNCHANGED M

Do(i) ==
  /\ i \in Proc
  /\ pc[i] = "act"
  /\ M' = [M EXCEPT ![i] = NextValue(i)]
  /\ pc' = [pc EXCEPT ![i] = "try"]

Next ==
  \E i \in Proc : Check(i) \/ Do(i)

ProcAct(i) == Check(i) \/ Do(i)

vars == << M, pc >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(ProcAct(i))

=============================================================================