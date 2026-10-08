----------------------------- MODULE TokenRing -----------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

(*
  Use K distinct counter values with K > N. We choose K = N + 1 to satisfy K > N
  without requiring an additional model constant.
*)
K == N + 1

Proc == 0..(N - 1)

VARIABLES val

vars == << val >>

TypeOK == val \in [Proc -> 0..(K - 1)]

Init == TypeOK

Inc(x) == (x + 1) % K

Holds(i) ==
  IF i = 0
    THEN val[0] = val[N - 1]
    ELSE val[i] # val[i - 1]

Step(i) ==
  IF i = 0 THEN
    /\ Holds(0)
    /\ val' = [val EXCEPT ![0] = Inc(@)]
  ELSE
    /\ Holds(i)
    /\ val' = [val EXCEPT ![i] = val[i - 1]]

Next == \E i \in Proc: Step(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc: WF_vars(Step(i))

SomeoneHoldsToken == []( \E i \in Proc: Holds(i) )

UniqueToken ==
  \E i \in Proc:
    /\ Holds(i)
    /\ \A j \in Proc: j # i => ~Holds(j)

EventuallyJustOneHoldsToken == <>[] UniqueToken

============================================================================