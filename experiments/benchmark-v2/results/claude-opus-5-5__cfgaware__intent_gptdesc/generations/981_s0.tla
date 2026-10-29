---------------------------- MODULE Alternation ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Two-party alternation (handshake) protocol between a Producer and a      *)
(* Consumer.  Control variables p (producer phase bit) and c (consumer      *)
(* phase bit) enforce strict alternation:                                   *)
(*   p = c  : the Producer is enabled                                       *)
(*   p # c  : the Consumer is enabled                                       *)
(* The shared payload x is updated by an abstract relation XAct and         *)
(* initialized by the predicate XInit, so that control-flow properties do   *)
(* not depend on a concrete payload implementation.                         *)
(***************************************************************************)

VARIABLES p, c, x

vars == <<p, c, x>>

(***************************************************************************)
(* Payload relation.  XInit(d) is the initialization predicate for the      *)
(* payload.  XAct(i, d, dp) is the per-step transition relation: party i    *)
(* (0 = Producer, 1 = Consumer) may change the payload from d to dp.        *)
(* These definitions are one admissible instantiation of the abstract       *)
(* relation and may be overridden in the model configuration.               *)
(***************************************************************************)
Data == {0, 1, 2}

XInit(d) == d \in Data

XAct(i, d, dp) == /\ dp \in Data
                  /\ IF i = 0 THEN dp = (d + 1) % 3   \* Producer writes
                              ELSE dp = d             \* Consumer reads

-----------------------------------------------------------------------------
(* Initial condition *)
Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

(* Producer acts when phases agree; then flips its bit. *)
ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

(* Consumer acts when phases differ; then flips its bit. *)
ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(ProducerStep) /\ WF_vars(ConsumerStep)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ p \in {0, 1}
          /\ c \in {0, 1}

\* Exactly one of the two parties is enabled at any time.
ExactlyOneEnabled == (p = c) # (p # c)

ProducerEnabled == p = c
ConsumerEnabled == p # c

Inv == /\ TypeOK
       /\ ExactlyOneEnabled
       /\ ~(ProducerEnabled /\ ConsumerEnabled)
       /\ (ProducerEnabled \/ ConsumerEnabled)

\* Roles alternate after each action.
Alternates ==
  [][ /\ ProducerStep => (p' # c')
      /\ ConsumerStep => (p' = c') ]_vars

-----------------------------------------------------------------------------
(* Refinement: an abstract alternating single bit.                         *)
(* The abstract bit is 0 when the Producer is enabled and 1 when the       *)
(* Consumer is enabled; it toggles on every action.                        *)

ABit == (p + c) % 2

AbsInit == ABit = 0

AbsNext == ((p' + c') % 2) = 1 - ABit

AbsSpec == AbsInit /\ [][AbsNext]_ABit

Refinement == AbsSpec

-----------------------------------------------------------------------------
(* Liveness / progress *)

\* Absence of deadlock: the payload relation permits the enabled party to act.
ProducerCanAct == \E dp \in Data : XAct(0, x, dp)
ConsumerCanAct == \E dp \in Data : XAct(1, x, dp)

NoDeadlock == [](ENABLED Next)

\* Under fairness, each party acts infinitely often.
ProducerProgress == []<>(p # c)
ConsumerProgress == []<>(p = c)

Progress == ProducerProgress /\ ConsumerProgress

THEOREM Spec => []Inv
THEOREM Spec => Alternates
THEOREM Spec => AbsSpec
THEOREM FairSpec => Progress
=============================================================================