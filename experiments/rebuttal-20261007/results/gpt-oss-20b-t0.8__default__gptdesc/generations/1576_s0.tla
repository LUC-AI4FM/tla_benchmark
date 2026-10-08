------------------------------ MODULE ConcurrentQueue ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N, OKAY, FULL, EMPTY, NULL

VARIABLES q, rV

vars == <<q, rV>>

TypeInv ==
  /\ q \in Seq(Val)
  /\ rV \in [Procs -> ({OKAY, FULL, EMPTY, NULL} ∪ Val)]

BoundInv == Len(q) <= N

Init ==
  /\ q = <<>>
  /\ rV = [p \in Procs |-> NULL]
  /\ TypeInv
  /\ BoundInv

EnqFront(p) ==
  ( Len(q) < N
    /\ ∃ v \in Val : (q' = <<<v>>> ^ q)
    /\ rV' = [rV EXCEPT ![p] = OKAY] )
 \/ ( Len(q) >= N
     /\ UNCHANGED <<q>>
     /\ rV' = [rV EXCEPT ![p] = FULL] )

EnqBack(p) ==
  ( Len(q) < N
    /\ ∃ v \in Val : (q' = q ^ <<<v>>>)
    /\ rV' = [rV EXCEPT ![p] = OKAY] )
 \/ ( Len(q) >= N
     /\ UNCHANGED <<q>>
     /\ rV' = [rV EXCEPT ![p] = FULL] )

DeqHead(p) ==
  ( Len(q) > 0
    /\ rV' = [rV EXCEPT ![p] = q[1]]
    /\ q' = SUBSEQ(q, 2, Len(q)) )
 \/ ( Len(q) = 0
     /\ UNCHANGED <<q>>
     /\ rV' = [rV EXCEPT ![p] = EMPTY] )

DeqTail(p) ==
  ( Len(q) > 0
    /\ rV' = [rV EXCEPT ![p] = q[Len(q)]]
    /\ q' = SUBSEQ(q, 1, Len(q)-1) )
 \/ ( Len(q) = 0
     /\ UNCHANGED <<q>>
     /\ rV' = [rV EXCEPT ![p] = EMPTY] )

P(p) == EnqFront(p) \/ EnqBack(p) \/ DeqHead(p) \/ DeqTail(p)

STUTTER == /\ UNCHANGED <<q, rV>>

Next ==
  \/ ∃ p \in Procs : P(p)
     \/ STUTTER

Spec ==
  Init
  /\ [][Next]_vars
  /\ []BoundInv
  /\ (∀p \in Procs : WF_0(P(p)))

=============================================================================