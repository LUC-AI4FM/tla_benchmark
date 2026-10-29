-------------------------- MODULE AlternatingBitEnv --------------------------
(***************************************************************************)
(* Alternating Bit Protocol with an environment process.                   *)
(*                                                                         *)
(* The environment produces data values into a pending queue (envQ).       *)
(* The sender (A) takes values from envQ and sends them tagged with an     *)
(* alternating bit over the lossy FIFO channel AtoB. The receiver (B)      *)
(* acknowledges by sending its current bit over the lossy FIFO channel     *)
(* BtoA. When A receives an ack equal to its current bit, it takes the     *)
(* next pending value from envQ and flips its bit.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Data,      \* finite set of data values, e.g. {"Fred","Mary","Ted"}
          MaxQLen    \* bound on the length of every queue, for model checking

ASSUME MaxQLen \in Nat \ {0}

VARIABLES AVar,   \* sender's current <<value, bit>>
          BVar,   \* receiver's last accepted <<value, bit>>
          AtoB,   \* message channel: sequence of <<value, bit>>
          BtoA,   \* acknowledgment channel: sequence of bits
          envQ    \* values produced by the environment, not yet taken by A

vars    == <<AVar, BVar, AtoB, BtoA, envQ>>
absVars == <<AVar, BVar, envQ>>

Bits == {0, 1}
Msgs == Data \X Bits

-----------------------------------------------------------------------------
(* Helper operators *)

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(* A sequence consisting of at most two contiguous blocks of equal elements *)
TwoValues(q) ==
  \A i, j \in 1..(Len(q) - 1) :
     (q[i] # q[i + 1] /\ q[j] # q[j + 1]) => i = j

-----------------------------------------------------------------------------
(***************************************************************************)
(* High-level specification: ABP with environment (no channels).           *)
(***************************************************************************)

ABEInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ envQ = << >>

EnvProduce ==
  /\ Len(envQ) < MaxQLen
  /\ \E d \in Data : envQ' = Append(envQ, d)
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

ABE_EnvProduce ==
  /\ Len(envQ) < MaxQLen
  /\ \E d \in Data : envQ' = Append(envQ, d)
  /\ UNCHANGED <<AVar, BVar>>

ABE_A ==
  /\ AVar = BVar
  /\ envQ # << >>
  /\ AVar' = <<Head(envQ), 1 - AVar[2]>>
  /\ envQ' = Tail(envQ)
  /\ UNCHANGED BVar

ABE_B ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ UNCHANGED <<AVar, envQ>>

ABENext == ABE_EnvProduce \/ ABE_A \/ ABE_B

ABESpec == ABEInit /\ [][ABENext]_absVars /\ WF_absVars(ABE_B)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Implementation: Alternating Bit Protocol over lossy FIFO channels.      *)
(***************************************************************************)

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ envQ = << >>

(* Sender (re)transmits its current message *)
ASnd ==
  /\ Len(AtoB) < MaxQLen
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, envQ>>

(* Sender receives an acknowledgment; on a matching ack with a pending     *)
(* value available it adopts the next value and flips its bit.             *)
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar[2] /\ envQ # << >>
       THEN /\ AVar' = <<Head(envQ), 1 - AVar[2]>>
            /\ envQ' = Tail(envQ)
       ELSE UNCHANGED <<AVar, envQ>>
  /\ UNCHANGED <<BVar, AtoB>>

(* Receiver (re)sends an acknowledgment carrying its current bit *)
BSnd ==
  /\ Len(BtoA) < MaxQLen
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB, envQ>>

(* Receiver receives a message; accepts it if it carries a new bit *)
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ UNCHANGED <<AVar, BtoA, envQ>>

(* Channels are unreliable: any message in transit may be lost *)
LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
        /\ UNCHANGED BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar, envQ>>

Next == EnvProduce \/ ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq(Bits)
  /\ envQ \in Seq(Data)

BoundedQueues ==
  /\ Len(AtoB) <= MaxQLen
  /\ Len(BtoA) <= MaxQLen
  /\ Len(envQ) <= MaxQLen

(* State constraint usable by TLC *)
QueueConstraint == BoundedQueues

(* If an acknowledgment matching the sender's bit is in transit, the       *)
(* sender and receiver agree on the current value.                         *)
Consistency ==
  \A i \in 1..Len(BtoA) : BtoA[i] = AVar[2] => AVar = BVar

(* Any message in transit carrying the sender's current bit carries the    *)
(* sender's current value.                                                 *)
MsgConsistency ==
  \A i \in 1..Len(AtoB) : AtoB[i][2] = AVar[2] => AtoB[i] = AVar

(* Messages in transit form at most two distinct consecutive blocks *)
SequenceStability ==
  /\ TwoValues(AtoB)
  /\ TwoValues(BtoA)

Inv ==
  /\ TypeOK
  /\ BoundedQueues
  /\ Consistency
  /\ MsgConsistency
  /\ SequenceStability

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

(* Every value adopted by the sender is eventually delivered to the receiver *)
Delivery == (AVar # BVar) ~> (AVar = BVar)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)

THEOREM Spec => []Inv
THEOREM Spec => Delivery
THEOREM Refinement == Spec => ABESpec
=============================================================================