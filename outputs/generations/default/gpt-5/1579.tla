---- MODULE DijkstraTokenRing ----
EXTENDS Naturals, FiniteSets, TLC

(*
Dijkstra's first self-stabilizing token ring (PlusCal)

  - Ring of N > 0 processes indexed 0..N-1
  - Local values are in 0..K-1 with K > N
  - Process 0 increments its value modulo K when its value equals that of process N-1
  - Every other process i > 0 copies its predecessor when their values differ
  - A token is at i iff (i = 0 /\ val[0] = val[N-1]) \/ (i > 0 /\ val[i] # val[i-1])
  - Weak fairness for each process action

--algorithm DijkstraRing
variables
  \* deterministic initial values in PlusCal; the TLA+ spec below allows arbitrary initial values
  val = [i \in 0..(N-1) |-> 0];

fair process (P \in 0..(N-1))
begin
Loop:
  if P = 0 then
    when val[0] = val[N-1];
    val[0] := (val[0] + 1) % K;
  else
    when val[P] # val[P-1];
    val[P] := val[P-1];
  end if;
  goto Loop;
end process
end algorithm
*)

CONSTANTS N, K

ASSUME
  /\ N \in Nat /\ N > 0
  /\ K \in Nat /\ K > N

Proc == 0..(N-1)
ValDom == 0..(K-1)

VARIABLES val

vars == << val >>

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

TypeOK ==
  /\ val \in [Proc -> ValDom]

Token(i) ==
  IF i = 0
    THEN val[0] = val[N-1]
    ELSE val[i] # val[i-1]

TokenHolders == { i \in Proc : Token(i) }
TokensCount == Cardinality(TokenHolders)

HasSomeToken == TokensCount >= 1
Legit == TokensCount = 1

Init ==
  /\ val \in [Proc -> ValDom]

Step(i) ==
  /\ i \in Proc
  /\ IF i = 0
        THEN /\ val[0] = val[N-1]
             /\ val' = [val EXCEPT ![0] = (val[0] + 1) % K]
        ELSE /\ val[i] # val[i-1]
             /\ val' = [val EXCEPT ![i] = val[i-1]]

Next ==
  \E i \in Proc : Step(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Step(i))

THEOREM Spec => []TypeOK

THEOREM Spec => []HasSomeToken

THEOREM Spec => <>([]Legit)

====