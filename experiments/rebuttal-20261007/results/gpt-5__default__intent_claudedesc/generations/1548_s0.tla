----------------------------- MODULE OneStepByzConsensus -----------------------------

EXTENDS Integers, Naturals, FiniteSets, Sequences

CONSTANTS
  N, T, F,
  UNDEC, Nil

(*
  Constants assumptions (static model parameters)
*)
ASSUME /\ N \in Nat
       /\ T \in Nat
       /\ F \in Nat
       /\ F \leq T
       /\ N > 3*T
       /\ N > 0

(*
  Processes and values
*)
Proc == 1..N
Val  == {0, 1}
DecVal == Val \cup {UNDEC}

(*
  State variables
  - Byz      : the (fixed) set of Byzantine processes (size at most F)
  - prop     : initial proposals (0 or 1) of each process
  - sentC    : whether a correct process has broadcast its proposal
  - d        : decision state of each process (UNDEC, 0, or 1)
  - recv0C/1C: per-receiver counts of 0/1 messages received from correct senders
  - recv0B/1B: per-receiver counts of 0/1 messages received from Byzantine senders
  - bmsg     : for each sender and receiver, Byzantine senders may send at most one message
               per receiver (Nil means none so far, otherwise 0 or 1). For correct
               senders, this remains Nil and their broadcast is modeled by sentC.
*)
VARIABLES
  Byz,
  prop,
  sentC,
  d,
  recv0C, recv1C,
  recv0B, recv1B,
  bmsg

Correct == Proc \ Byz

(*
  Helper counters for a process q
*)
ZeroCount(q) == recv0C[q] + recv0B[q]
OneCount(q)  == recv1C[q] + recv1B[q]
TotalCount(q) == ZeroCount(q) + OneCount(q)

(*
  Initial condition
*)
Init ==
  /\ Byz \subseteq Proc
  /\ Cardinality(Byz) \leq F
  /\ prop \in [Proc -> Val]
  /\ sentC \in [Proc -> BOOLEAN]
  /\ \A p \in Proc: sentC[p] = FALSE
  /\ d \in [Proc -> DecVal]
  /\ \A p \in Proc: d[p] = UNDEC
  /\ recv0C \in [Proc -> 0..N]
  /\ recv1C \in [Proc -> 0..N]
  /\ recv0B \in [Proc -> 0..N]
  /\ recv1B \in [Proc -> 0..N]
  /\ \A q \in Proc:
        /\ recv0C[q] = 0
        /\ recv1C[q] = 0
        /\ recv0B[q] = 0
        /\ recv1B[q] = 0
  /\ bmsg \in [Proc -> [Proc -> ({Nil} \cup Val)]]
  /\ \A s \in Proc: \A r \in Proc: bmsg[s][r] = Nil

(*
  A correct process p broadcasts its proposal to everyone (one-step broadcast).
  This increases, for all receivers q, the correct-message count of the value sent.
*)
Propose(p) ==
  /\ p \in Correct
  /\ ~sentC[p]
  /\ LET inc0 == IF prop[p] = 0 THEN 1 ELSE 0
         inc1 == IF prop[p] = 1 THEN 1 ELSE 0
     IN
     /\ sentC' = [sentC EXCEPT ![p] = TRUE]
     /\ recv0C' = [q \in Proc |-> recv0C[q] + inc0]
     /\ recv1C' = [q \in Proc |-> recv1C[q] + inc1]
     /\ UNCHANGED << Byz, prop, d, recv0B, recv1B, bmsg >>

(*
  A Byzantine sender b may send at most one message to any receiver q, with arbitrary bit v.
*)
ByzantineSend(b, q, v) ==
  /\ b \in Byz
  /\ q \in Proc
  /\ v \in Val
  /\ bmsg[b][q] = Nil
  /\ bmsg'  = [bmsg EXCEPT ![b][q] = v]
  /\ recv0B' = [recv0B EXCEPT ![q] = recv0B[q] + IF v = 0 THEN 1 ELSE 0]
  /\ recv1B' = [recv1B EXCEPT ![q] = recv1B[q] + IF v = 1 THEN 1 ELSE 0]
  /\ UNCHANGED << Byz, prop, sentC, d, recv0C, recv1C >>

(*
  A correct process p decides once it has received at least N-T total messages.
  It decides 0 if ZeroCount >= N-T, 1 if OneCount >= N-T, otherwise falls back to its own proposal.
*)
Decide(p) ==
  /\ p \in Correct
  /\ d[p] = UNDEC
  /\ TotalCount(p) >= N - T
  /\ d' = [d EXCEPT ![p] =
              IF ZeroCount(p) >= N - T THEN 0
              ELSE IF OneCount(p) >= N - T THEN 1
              ELSE prop[p] ]
  /\ UNCHANGED << Byz, prop, sentC, recv0C, recv1C, recv0B, recv1B, bmsg >>

(*
  Next-state relation
*)
Next ==
  \/ \E p \in Correct: Propose(p)
  \/ \E p \in Correct: Decide(p)
  \/ \E b \in Byz, q \in Proc, v \in Val: ByzantineSend(b, q, v)

Vars == << Byz, prop, sentC, d, recv0C, recv1C, recv0B, recv1B, bmsg >>

(*
  Weak fairness: each correct process eventually proposes and decides (if continuously enabled).
*)
Fairness ==
  \A p \in Proc:
    (p \in Correct) =>
      ( WF_Vars(Propose(p)) /\ WF_Vars(Decide(p)) )

Spec ==
  Init /\ [][Next]_Vars /\ Fairness

(*
  Safety/type invariants
*)
TypeInv ==
  /\ Byz \subseteq Proc
  /\ Cardinality(Byz) \leq F
  /\ prop \in [Proc -> Val]
  /\ sentC \in [Proc -> BOOLEAN]
  /\ d \in [Proc -> DecVal]
  /\ recv0C \in [Proc -> 0..N]
  /\ recv1C \in [Proc -> 0..N]
  /\ recv0B \in [Proc -> 0..N]
  /\ recv1B \in [Proc -> 0..N]
  /\ bmsg \in [Proc -> [Proc -> ({Nil} \cup Val)]]
  /\ \A q \in Proc:
        /\ recv0C[q] = Cardinality({ p \in Correct: sentC[p] /\ prop[p] = 0 })
        /\ recv1C[q] = Cardinality({ p \in Correct: sentC[p] /\ prop[p] = 1 })
        /\ recv0B[q] = Cardinality({ b \in Byz: bmsg[b][q] = 0 })
        /\ recv1B[q] = Cardinality({ b \in Byz: bmsg[b][q] = 1 })
        /\ recv0B[q] + recv1B[q] = Cardinality({ b \in Byz: bmsg[b][q] # Nil })
  /\ \A p \in Proc: d[p] \in DecVal

(*
  Initialization predicates used in properties
*)
AllCorrectZeroInit == \A p \in Correct: prop[p] = 0
AllCorrectOneInit  == \A p \in Correct: prop[p] = 1
AllOnesInit        == \A p \in Proc: prop[p] = 1

(*
  Key correctness properties (to be checked against Spec)
  1) If all correct initially propose 0, then no correct process ever decides 1,
     and eventually all correct decide (hence they must decide 0).
*)
Safety_AllZero ==
  AllCorrectZeroInit => []( \A p \in Correct: d[p] # 1 )

Liveness_AllZero ==
  AllCorrectZeroInit => []<>( \A p \in Correct: d[p] \in Val )

(*
  2) If all correct initially propose 1, they all eventually decide 1.
*)
Liveness_AllOne ==
  AllCorrectOneInit => []<>( \A p \in Correct: d[p] = 1 )

(*
  3) Under all-ones initialization, every correct process eventually decides 1.
*)
Liveness_AllOnes_Global ==
  AllOnesInit => []<>( \A p \in Correct: d[p] = 1 )

=============================================================================