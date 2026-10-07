----------------------------- MODULE DijkstraTokenRing -----------------------------

EXTENDS Naturals, Integers, FiniteSets

(*
Dijkstra's first self-stabilizing token ring (PlusCal sketch, for reference):

--algorithm DijTokenRing
variables x \in [0..N-1 -> 0..K-1];

fair process p \in 0..N-1
begin
P:
  if p = 0 then
    if x[p] = x[(p - 1) % N] then
      x[p] := (x[p] + 1) % K;
    end if;
  else
    if x[p] # x[p-1] then
      x[p] := x[p-1];
    end if;
  end if;
  goto P;
end process;

end algorithm
*)

CONSTANTS N, K

ASSUME N \in Nat /\ N > 0 /\ K \in Nat /\ K > N

VARIABLES x

Proc == 0 .. (N - 1)
Val  == 0 .. (K - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

TypeInv == x \in [Proc -> Val]

Token(i) ==
  IF i = 0
    THEN x[i] = x[Pred(i)]
    ELSE x[i] # x[Pred(i)]

TokenSet == { i \in Proc : Token(i) }
SomeToken == \E i \in Proc : Token(i)
OneToken == Cardinality(TokenSet) = 1

NewVal(i) ==
  IF i = 0
    THEN (x[i] + 1) % K
    ELSE x[Pred(i)]

Step(i) ==
  /\ Token(i)
  /\ x' = [x EXCEPT ![i] = NewVal(i)]

Next == \E i \in Proc : Step(i)

Init == TypeInv

vars == << x >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Step(i))

THEOREM TypeOK == Spec => []TypeInv

THEOREM TokensAlways == Spec => [](SomeToken)

THEOREM ConvergesToSingleToken == Spec => <>[]OneToken

=============================================================================