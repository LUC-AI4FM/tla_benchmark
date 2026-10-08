------------------------------ MODULE DijkstraTokenRing ------------------------------
CONSTANTS N, K

ASSUME
  N > 0 /\ K > N

VARIABLES M, pc

(* Helper definitions *)
Token(i) == IF i = 0 THEN M[0] = M[N-1] ELSE M[i] # M[i-1]

Update(M,i) ==
  IF i = 0
     THEN [M EXCEPT ![0] = (M[0]+1) Mod K]
     ELSE [M EXCEPT ![i] = M[i-1]]

Step(i) ==
  ((pc[i] = "Check" /\ Token(i) /\ pc' = [pc EXCEPT ![i] = "Assign"] /\ M' = M)
   \/ (pc[i] = "Assign" /\ pc' = [pc EXCEPT ![i] = "Check"] /\ M' = Update(M,i)))

Next == \E i \in 0..N-1 : Step(i)

Init ==
  /\ M \in [0..N-1 -> 0..K-1]
  /\ pc = [i \in 0..N-1 |-> "Check"]

Spec == Init /\ [][Next]_(M,pc) /\ WF_vars(Next)

(* Invariants *)
SomeoneHoldsToken == \E i \in 0..N-1 : Token(i)

ExactlyOneToken ==
  \E i \in 0..N-1 :
    (Token(i) /\ \A j \in 0..N-1 : (j = i \/ ~Token(j)))

EventuallyJustOneHoldsToken == <> [] ExactlyOneToken

=============================================================================