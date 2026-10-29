--------------------------- MODULE MCAlternatingBit ---------------------------
EXTENDS AlternatingBit, Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Model-checking harness for the alternating-bit protocol specification   *)
(* imported from module AlternatingBit.  That module is assumed to define  *)
(* the constant Data, the variables msgQ, ackQ, sBit, sAck, rBit, sent,    *)
(* rcvd, and the operators ABInit, ABNext, ABTypeInv, ABFairness, ABSpec   *)
(* and abvars.                                                             *)
(***************************************************************************)

(***************************************************************************)
(* Aliases for the imported initial predicate and next-state action.       *)
(***************************************************************************)
Init == ABInit

Next == ABNext

(***************************************************************************)
(* State constraint that bounds both message queues so the state space is  *)
(* finite.                                                                 *)
(***************************************************************************)
SeqConstraint == /\ Len(msgQ) \leq 2
                 /\ Len(ackQ) \leq 2

(***************************************************************************)
(* Safety: type correctness of the imported protocol.                      *)
(***************************************************************************)
TypeOK == ABTypeInv

(***************************************************************************)
(* Liveness: a value that has been sent but not yet acknowledged is        *)
(* eventually received.                                                    *)
(***************************************************************************)
SentLeadsToRcvd ==
    \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

(***************************************************************************)
(* Temporal property claiming that the protocol bits may disagree forever. *)
(* TLC is expected to find a violation of its negation, or to show that    *)
(* the bits can remain permanently different.                              *)
(***************************************************************************)
BitsEventuallyDisagreeForever == <>[](sBit # sAck)

NoPermanentDisagreement == ~BitsEventuallyDisagreeForever

(***************************************************************************)
(* Derived action-temporal formula: weak fairness, with subscript msgQ, of *)
(* the action that makes the type invariant false in the next state.       *)
(***************************************************************************)
TNext == WF_msgQ(~ABTypeInv')

(***************************************************************************)
(* Stability property over sent data: once a value has been sent, it       *)
(* remains the sent value forever.                                         *)
(***************************************************************************)
TProp == \A d \in Data : (sent = d) => [](sent = d)

(***************************************************************************)
(* Combined specification: the imported spec together with the added       *)
(* temporal condition.                                                     *)
(***************************************************************************)
CSpec == ABSpec /\ TNext

Spec == CSpec

(***************************************************************************)
(* Postcondition checked by TLC after model checking.  It records the      *)
(* structure of the counterexample TLC reports.  The counterexample is a   *)
(* record with a "state" field and an "action" field.  The "state" field   *)
(* is a sequence of <<index, state>> pairs.  The "action" field is a set   *)
(* of <<<<i, s>>, actionInfo, <<j, t>>>> triples.                          *)
(***************************************************************************)
CounterExample == TLCGet("counterexample")

PostCondition ==
    LET cex == CounterExample
    IN  /\ DOMAIN cex = {"state", "action"}
        /\ \A i \in 1..Len(cex.state) :
              /\ cex.state[i][1] = i
              /\ cex.state[i][2].sent \in Data
              /\ cex.state[i][2].rcvd \in Data
              /\ cex.state[i][2].sBit \in {0, 1}
              /\ cex.state[i][2].sAck \in {0, 1}
              /\ cex.state[i][2].rBit \in {0, 1}
        /\ \A a \in cex.action :
              /\ a[1][1] \in 1..Len(cex.state)
              /\ a[3][1] \in 1..Len(cex.state)
              /\ a[1][2] = cex.state[a[1][1]][2]
              /\ a[3][2] = cex.state[a[3][1]][2]
        /\ Len(cex.state) > 0 =>
              \E a \in cex.action : a[1][1] = Len(cex.state)
=============================================================================