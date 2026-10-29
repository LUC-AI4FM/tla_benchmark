------------------------------- MODULE TwoPartyHandshake -------------------------------
(***************************************************************************)
(* Two-party alternation (handshake) protocol between a Producer and a     *)
(* Consumer. Each party owns one control bit: p for the Producer and c for *)
(* the Consumer.                                                           *)
(*   - When p = c the bits are in phase, so the Producer is enabled.       *)
(*   - When p # c the Consumer is enabled.                                 *)
(* The Producer acts by flipping p and the Consumer acts by flipping c.    *)
(* Both parties may read and update a shared payload `box`. The payload    *)
(* behaviour is abstracted by the parameter relations PayloadInit,         *)
(* ProducerStep and ConsumerStep, so that reasoning about the control      *)
(* flow does not depend on a concrete payload implementation.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    Data,               \* set of possible payload values
    PayloadInit(_),     \* PayloadInit(d): d is an allowed initial payload
    ProducerStep(_, _), \* ProducerStep(d, e): Producer may change payload d to e
    ConsumerStep(_, _)  \* ConsumerStep(d, e): Consumer may change payload d to e

(***************************************************************************)
(* Well-formedness assumptions on the payload parameters. The second and   *)
(* third assumptions say that each party can always perform its update.    *)
(* They are needed only for progress (deadlock freedom and liveness), not  *)
(* for the control-flow safety properties.                                 *)
(***************************************************************************)
ASSUME PayloadInitNonEmpty == \E d \in Data : PayloadInit(d)

ASSUME ProducerTotal == \A d \in Data : \E e \in Data : ProducerStep(d, e)

ASSUME ConsumerTotal == \A d \in Data : \E e \in Data : ConsumerStep(d, e)

VARIABLES
    p,    \* Producer's control bit
    c,    \* Consumer's control bit
    box   \* shared payload

vars == <<p, c, box>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete specification                                                  *)
(***************************************************************************)
Init ==
    /\ p = 0
    /\ c = 0
    /\ box \in Data
    /\ PayloadInit(box)

\* The Producer is enabled exactly when the bits are in phase.
Produce ==
    /\ p = c
    /\ box' \in Data
    /\ ProducerStep(box, box')
    /\ p' = 1 - p
    /\ UNCHANGED c

\* The Consumer is enabled exactly when the bits are out of phase.
Consume ==
    /\ p # c
    /\ box' \in Data
    /\ ConsumerStep(box, box')
    /\ c' = 1 - c
    /\ UNCHANGED p

Next == Produce \/ Consume

Fairness == WF_vars(Produce) /\ WF_vars(Consume)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* The control variables always remain within the two permitted phases.
TypeOK ==
    /\ p \in {0, 1}
    /\ c \in {0, 1}
    /\ box \in Data

\* Exactly one party's turn is indicated by the control state.
ProducerTurn == p = c
ConsumerTurn == p # c

ControlExclusive == ProducerTurn # ConsumerTurn

\* Exactly one of the two actions is enabled in every reachable state.
\* This relies on the totality assumptions ProducerTotal and ConsumerTotal.
ExactlyOneEnabled ==
    /\ (ENABLED Produce) \/ (ENABLED Consume)
    /\ ~((ENABLED Produce) /\ (ENABLED Consume))

\* Roles alternate after each action: a Producer step hands the turn to the
\* Consumer, and a Consumer step hands the turn back to the Producer.
AlternationStep ==
    [][ /\ Produce => (ProducerTurn /\ ConsumerTurn')
        /\ Consume => (ConsumerTurn /\ ProducerTurn')
      ]_vars

\* The same consecutive party can never act twice in a row.
NoDoubleProduce == [][Produce => ~(ENABLED Produce)']_vars
NoDoubleConsume == [][Consume => ~(ENABLED Consume)']_vars

Inv == TypeOK /\ ControlExclusive

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement: an abstract alternating-bit specification.                  *)
(* The abstract state is a single bit `b` together with the payload.       *)
(* When b = 0 the Producer acts, when b = 1 the Consumer acts, and every   *)
(* action toggles b. The refinement mapping is b == (p + c) % 2, which is  *)
(* 0 when the bits are in phase and 1 when they are out of phase.          *)
(***************************************************************************)
ABit == (p + c) % 2

AbsInit(b, d) ==
    /\ b = 0
    /\ d \in Data
    /\ PayloadInit(d)

AbsNext(b, d) ==
    /\ b' = 1 - b
    /\ d' \in Data
    /\ \/ b = 0 /\ ProducerStep(d, d')
       \/ b = 1 /\ ConsumerStep(d, d')

AbsSpec ==
    /\ AbsInit(ABit, box)
    /\ [][AbsNext(ABit, box)]_<<ABit, box>>
    /\ WF_<<ABit, box>>(AbsNext(ABit, box))

\* The abstract bit always lies in {0,1} and identifies whose turn it is.
AbsBitOK == ABit \in {0, 1} /\ ((ABit = 0) <=> ProducerTurn)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness / progress                                                     *)
(***************************************************************************)

\* No deadlock: some action is always enabled (uses the totality assumptions).
DeadlockFree == [](ENABLED Next)

\* Each party acts infinitely often, so the alternation continues forever.
ProducerProgress == []<>(<<Produce>>_vars)
ConsumerProgress == []<>(<<Consume>>_vars)

\* Whenever it is one party's turn, the turn eventually passes to the other.
TurnHandoff ==
    /\ ProducerTurn ~> ConsumerTurn
    /\ ConsumerTurn ~> ProducerTurn

-----------------------------------------------------------------------------
THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM ControlSafety    == Spec => []ControlExclusive
THEOREM OneEnabled       == Spec => []ExactlyOneEnabled
THEOREM Alternates       == Spec => AlternationStep
THEOREM NoRepeat         == Spec => (NoDoubleProduce /\ NoDoubleConsume)
THEOREM AbsBit           == Spec => []AbsBitOK
THEOREM Refinement       == Spec => AbsSpec
THEOREM NoDeadlock       == Spec => DeadlockFree
THEOREM Progress         == Spec => (ProducerProgress /\ ConsumerProgress)
THEOREM Handoff          == Spec => TurnHandoff
=============================================================================