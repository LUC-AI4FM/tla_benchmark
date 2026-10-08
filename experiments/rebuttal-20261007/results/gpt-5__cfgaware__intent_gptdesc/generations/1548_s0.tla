------------------------------- MODULE OneStepByz -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

(*
  Assumptions on parameters:
  - N > 3*T and T >= F
  - N, T, F are natural numbers with N > 0
*)
ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 0 /\ N > 3*T /\ T >= F

(*
  Processes are indexed 1..N.
*)
Proc == 1..N

(*
  Variables:
  - B: set of Byzantine processes, fixed after initialization, with |B| <= F
  - proposal[p] in {0,1}: initial proposal of process p
  - cSent0, cSent1: total number of 0- and 1- votes sent by correct processes (exactly once)
  - bSent0, bSent1: abstract bounds on number of 0- and 1- votes that Byzantine processes may inject per receiver
  - rcv0[p], rcv1[p]: number of 0- and 1- votes received by process p so far (monotonic, bounded)
  - decision[p] in {"Init","Dec0","Dec1","Undecided"}: local decision state of p
  - sentDone: whether correct processes have performed their single broadcast
  - bSentDone: whether Byzantine vote bounds have been set
*)
VARIABLES
  B,
  proposal,
  cSent0, cSent1,
  bSent0, bSent1,
  rcv0, rcv1,
  decision,
  sentDone,
  bSentDone

vars == << B, proposal, cSent0, cSent1, bSent0, bSent1, rcv0, rcv1, decision, sentDone, bSentDone >>

Correct == Proc \ B
Faulty  == B

Thr == N - T

Min(a, b) == IF a <= b THEN a ELSE b

TotalRecv(p) == rcv0[p] + rcv1[p]

Max0 == Min(N, cSent0 + bSent0)
Max1 == Min(N, cSent1 + bSent1)

TypeOK ==
  /\ B \subseteq Proc
  /\ Cardinality(B) <= F
  /\ proposal \in [Proc -> {0,1}]
  /\ cSent0 \in 0..N /\ cSent1 \in 0..N
  /\ bSent0 \in 0..N /\ bSent1 \in 0..N
  /\ rcv0 \in [Proc -> 0..N] /\ rcv1 \in [Proc -> 0..N]
  /\ \A p \in Proc: rcv0[p] + rcv1[p] <= N
  /\ decision \in [Proc -> {"Init","Dec0","Dec1","Undecided"}]
  /\ sentDone \in BOOLEAN /\ bSentDone \in BOOLEAN
  /\ sentDone
        => /\ cSent0 + cSent1 = Cardinality(Correct)
           /\ cSent0 = Cardinality({p \in Correct: proposal[p] = 0})
           /\ cSent1 = Cardinality({p \in Correct: proposal[p] = 1})

Init ==
  /\ B \in SUBSET Proc
  /\ Cardinality(B) <= F
  /\ proposal \in [Proc -> {0,1}]
  /\ cSent0 = 0 /\ cSent1 = 0
  /\ bSent0 \in 0..N /\ bSent1 \in 0..N
  /\ rcv0 = [p \in Proc |-> 0]
  /\ rcv1 = [p \in Proc |-> 0]
  /\ decision = [p \in Proc |-> "Init"]
  /\ sentDone = FALSE
  /\ bSentDone = FALSE

SendCorrect ==
  /\ ~sentDone
  /\ cSent0' = Cardinality({p \in Proc \ B: proposal[p] = 0})
  /\ cSent1' = Cardinality({p \in Proc \ B: proposal[p] = 1})
  /\ sentDone' = TRUE
  /\ UNCHANGED << B, proposal, bSent0, bSent1, rcv0, rcv1, decision, bSentDone >>

SetByzSends ==
  /\ ~bSentDone
  /\ bSent0' \in 0..N
  /\ bSent1' \in 0..N
  /\ bSentDone' = TRUE
  /\ UNCHANGED << B, proposal, cSent0, cSent1, rcv0, rcv1, decision, sentDone >>

Receive(p) ==
  /\ p \in Proc
  /\ decision[p] = "Init"
  /\ \E new0, new1 \in 0..N:
       /\ rcv0[p] <= new0 /\ new0 <= Max0
       /\ rcv1[p] <= new1 /\ new1 <= Max1
       /\ new0 + new1 <= N
       /\ (new0 > rcv0[p] \/ new1 > rcv1[p])
       /\ rcv0' = [rcv0 EXCEPT ![p] = new0]
       /\ rcv1' = [rcv1 EXCEPT ![p] = new1]
       /\ UNCHANGED << B, proposal, cSent0, cSent1, bSent0, bSent1, decision, sentDone, bSentDone >>

Decide(p) ==
  /\ p \in Correct
  /\ decision[p] = "Init"
  /\ TotalRecv(p) >= Thr
  /\ IF rcv0[p] >= Thr THEN
        decision' = [decision EXCEPT ![p] = "Dec0"]
     ELSE IF rcv1[p] >= Thr THEN
        decision' = [decision EXCEPT ![p] = "Dec1"]
     ELSE
        decision' = [decision EXCEPT ![p] = "Undecided"]
  /\ UNCHANGED << B, proposal, cSent0, cSent1, bSent0, bSent1, rcv0, rcv1, sentDone, bSentDone >>

Next ==
  \/ SendCorrect
  \/ SetByzSends
  \/ \E p \in Proc: Receive(p)
  \/ \E p \in Proc: Decide(p)

Fairness ==
  /\ \A p \in Correct: WF_vars(Receive(p))
  /\ \A p \in Correct: WF_vars(Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

AllCorrectPropose(v) == \A p \in Correct: proposal[p] = v

OneStep0_Ltl ==
  []( AllCorrectPropose(0) => ~( \E p \in Correct: decision[p] = "Dec1") )

OneStep1_Ltl ==
  []( AllCorrectPropose(1) => ~( \E p \in Correct: decision[p] = "Dec0") )

AllDecideOne ==
  <>( \A p \in Correct: decision[p] = "Dec1" )

=============================================================================