MODULE DijkstraTokenRing
EXTENDS Naturals

CONSTANTS N, K

VARIABLE val

Pred(i) == (i - 1 + N) MOD N

Token(i) == val[i] # val[Pred(i)]

Action0 ==
  /\ val[0] = val[N-1]
  /\ val' = [val EXCEPT ![0] = (val[0]+1) MOD K]

Action_i(i) ==
  /\ 1 <= i < N
  /\ val[i] # val[i-1]
  /\ val' = [val EXCEPT ![i] = val[i-1]]

AllActions == Action0 \/ ∃i ∈ 1 .. N-1 : Action_i(i)

Next == AllActions

Init ==
  /\ val ∈ [0..N-1 -> 0..K-1]

SomeTokenInvariant == ∃i ∈ 0..N-1 : Token(i)
UniqueTokenInvariant ==
  ∃i ∈ 0..N-1 :
    Token(i) /\ ∀j ∈ 0..N-1 : (j # i => ¬Token(j))

Spec ==
  Init
  /\ [][Next]_val
  /\ WF_vars(Next)

THEOREM SomeTokenInvariantAlways: Spec => []SomeTokenInvariant
THEOREM EventuallyUniqueToken: Spec => <>UniqueTokenInvariant

===============================================================================