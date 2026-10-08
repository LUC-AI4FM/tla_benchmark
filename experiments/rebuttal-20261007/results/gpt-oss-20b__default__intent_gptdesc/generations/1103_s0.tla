MODULE AtomicCommit
EXTENDS Naturals, TLC

CONSTANTS Proc

VARIABLES vote, crashed, decision, R, recvVote, FD, M

(* Type definitions *)
VoteVal == {"YES","NO"}

Message == [src -> Proc, dst -> Proc, val -> VoteVal]

vars == <<vote, crashed, decision, R, recvVote, FD, M>>

Init ==
  /\ vote \in [Proc -> VoteVal]
  /\ crashed = [p ∈ Proc |-> FALSE]
  /\ decision = [p ∈ Proc |-> "NONE"]
  /\ R = [p ∈ Proc |-> {}]
  /\ recvVote = [p ∈ Proc |-> [q ∈ Proc |-> "NONE"]]
  /\ FD = [p ∈ Proc |-> [q ∈ Proc |-> FALSE]]
  /\ M = {}

SendVote(p) ==
  /\ p \in Proc
  /\ crashed[p] = FALSE
  /\ decision[p] = "NONE"
  /\ M' = M ∪ { [src |-> p, dst |-> q, val |-> vote[p]] : q \in Proc \ {p} }
  /\ UNCHANGED <<crashed, decision, R, recvVote, FD>>

ReceiveMsg(q) ==
  /\ q \in Proc
  /\ crashed[q] = FALSE
  /\ \E m \in M : m.dst = q
  /\ LET m0 == CHOOSE m \in M : m.dst = q IN
        M' = M \ {m0}
        R' = [R EXCEPT ![q] = R[q] ∪ {m0.src}]
        recvVote' = [recvVote EXCEPT ![q][m0.src] = m0.val]
        UNCHANGED <<crashed, vote, decision, FD>>

Crash(p) ==
  /\ p \in Proc
  /\ crashed[p] = FALSE
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, R, recvVote, FD, M>>

UpdateFD(p,q,b) ==
  /\ p \in Proc
  /\ q \in Proc
  /\ b \in BOOLEAN
  /\ FD' = [FD EXCEPT ![p][q] = b]
  /\ UNCHANGED <<vote, crashed, decision, R, recvVote, M>>

Decide(p) ==
  /\ p \in Proc
  /\ crashed[p] = FALSE
  /\ decision[p] = "NONE"
  /\ LET AliveSet == { q ∈ Proc : ¬FD[p][q] } IN
        /\ R[p] ⊇ AliveSet
        /\ decision' = [decision EXCEPT ![p] =
                         IF (\A q ∈ AliveSet : recvVote[p][q] = "YES")
                           THEN "COMMIT"
                           ELSE "ABORT"]
  /\ UNCHANGED <<vote, crashed, R, recvVote, FD, M>>

Next ==
  \/ \E p \in Proc : SendVote(p)
  \/ \E q \in Proc : ReceiveMsg(q)
  \/ \E p \in Proc : Crash(p)
  \/ \E p,q,b : UpdateFD(p,q,b)
  \/ \E p \in Proc : Decide(p)

Spec == Init /\ [][Next]_vars

(* Safety invariants *)
AgreementInv ==
  \A p q ∈ Proc :
    /\ crashed[p] = FALSE
    /\ crashed[q] = FALSE
    /\ decision[p] ≠ "NONE"
    /\ decision[q] ≠ "NONE"
    => decision[p] = decision[q]

ValidityInv ==
  \A p ∈ Proc :
    /\ crashed[p] = FALSE
    /\ decision[p] = "COMMIT"
    => \A q ∈ Proc : vote[q] = "YES"

Safety == AgreementInv /\ ValidityInv

(* Liveness property *)
Liveness ==
  \A p ∈ Proc :
    /\ crashed[p] = FALSE
    => ◇(decision[p] ≠ "NONE")

THEOREM Spec => Safety
THEOREM Spec => Liveness

END MODULE