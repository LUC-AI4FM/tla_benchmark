------------------------------ MODULE Paxos ------------------------------

EXTENDS Naturals, FiniteSets, TLC

(*
  Paxos without explicit leaders or learners.
  We model the exchange of Prepare, Promise, Accept, Accepted, and Decide messages.
  Quorums are strict majorities with pairwise intersection.
  Liveness is intentionally not assumed (see FLP): termination is not guaranteed under asynchrony.
*)

CONSTANTS
  Proposers,   \* set of proposers
  Acceptors,   \* set of acceptors
  Values,      \* set of client values
  Ballots      \* finite set of ballot numbers (subset of Nat)

ASSUME
  /\ Proposers # {}
  /\ Acceptors # {}
  /\ Ballots   # {}
  /\ Ballots \subseteq Nat

(*
  Distinguished atoms for "no value" and "null ballot".
  NullBal is an integer not in Ballots (we pick -1).
*)
NullBal == -1
NoVal   == "NoVal"

Agents == Proposers \cup Acceptors

MsgTypes == {"Prepare","Promise","Accept","Accepted","Decide"}

(*
  Messages are records with uniform fields. Some fields are ignored depending on type.
*)
Message ==
  { [ type |-> t,
      from |-> f,
      to   |-> g,
      bal  |-> b,
      val  |-> v,
      aBal |-> ab ] :
      /\ t \in MsgTypes
      /\ f \in Agents
      /\ g \in (Agents \cup {"ALL"})
      /\ b \in (Ballots \cup {NullBal})
      /\ v \in (Values \cup {NoVal})
      /\ ab \in (Ballots \cup {NullBal})
  }

(*
  Majority quorum over Acceptors: strict majority ensures pairwise intersection.
*)
Quorum(S) == S \subseteq Acceptors /\ 2 * Cardinality(S) > Cardinality(Acceptors)

VARIABLES
  msgs,       \* set of sent messages
  aMaxBal,    \* [Acceptors -> Ballots \cup {NullBal}], highest promised ballot
  aAccBal,    \* [Acceptors -> Ballots \cup {NullBal}], highest accepted ballot
  aAccVal,    \* [Acceptors -> Values \cup {NoVal}], value accepted at aAccBal (or NoVal)
  decision    \* representative learned/decided value (or NoVal)

vars == << msgs, aMaxBal, aAccBal, aAccVal, decision >>

Init ==
  /\ msgs = {}
  /\ aMaxBal = [ a \in Acceptors |-> NullBal ]
  /\ aAccBal = [ a \in Acceptors |-> NullBal ]
  /\ aAccVal = [ a \in Acceptors |-> NoVal ]
  /\ decision = NoVal

PaxosTypeOK ==
  /\ msgs \subseteq Message
  /\ aMaxBal \in [Acceptors -> (Ballots \cup {NullBal})]
  /\ aAccBal \in [Acceptors -> (Ballots \cup {NullBal})]
  /\ aAccVal \in [Acceptors -> (Values  \cup {NoVal})]
  /\ \A a \in Acceptors : (aAccBal[a] = NullBal) <=> (aAccVal[a] = NoVal)
  /\ \A a \in Acceptors : aAccBal[a] = NullBal \/ aMaxBal[a] >= aAccBal[a]
  /\ decision \in (Values \cup {NoVal})

(*
  Helper: values that have been proposed in the accept phase.
*)
ProposedVals == { m.val : m \in msgs /\ m.type = "Accept" }

(*
  Actions
*)

SendPrepare ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    LET m == [ type |-> "Prepare", from |-> p, to |-> a, bal |-> b, val |-> NoVal, aBal |-> NullBal ]
    IN /\ msgs' = msgs \cup { m }
       /\ UNCHANGED << aMaxBal, aAccBal, aAccVal, decision >>

Promise ==
  \E a \in Acceptors, p \in Proposers, b \in Ballots :
    /\ \E m \in msgs : /\ m.type = "Prepare"
                       /\ m.from = p
                       /\ m.to   = a
                       /\ m.bal  = b
    /\ b > aMaxBal[a]
    /\ LET prom == [ type |-> "Promise", from |-> a, to |-> p, bal |-> b, val |-> aAccVal[a], aBal |-> aAccBal[a] ]
       IN /\ prom \notin msgs
          /\ msgs'    = msgs \cup { prom }
          /\ aMaxBal' = [aMaxBal EXCEPT ![a] = b]
          /\ UNCHANGED << aAccBal, aAccVal, decision >>

SendAccept ==
  \E p \in Proposers, a \in Acceptors, b \in Ballots :
    LET promMsgs == { m \in msgs : /\ m.type = "Promise" /\ m.to = p /\ m.bal = b } IN
    /\ Quorum({ m.from : m \in promMsgs })
    /\ LET nonEmptyHighest == { m \in promMsgs : m.aBal # NullBal } IN
       LET v ==
         IF nonEmptyHighest = {}
           THEN CHOOSE u \in Values : TRUE
           ELSE LET maxb == Max({ m.aBal : m \in nonEmptyHighest })
                IN  CHOOSE u \in { m.val : m \in nonEmptyHighest /\ m.aBal = maxb } : TRUE
       IN LET accm == [ type |-> "Accept", from |-> p, to |-> a, bal |-> b, val |-> v, aBal |-> NullBal ]
          IN /\ accm \notin msgs
             /\ msgs' = msgs \cup { accm }
             /\ UNCHANGED << aMaxBal, aAccBal, aAccVal, decision >>

AcceptAndAck ==
  \E a \in Acceptors, p \in Proposers, b \in Ballots, v \in Values :
    /\ \E m \in msgs : /\ m.type = "Accept"
                       /\ m.from = p
                       /\ m.to   = a
                       /\ m.bal  = b
                       /\ m.val  = v
    /\ b >= aMaxBal[a]
    /\ LET ack == [ type |-> "Accepted", from |-> a, to |-> p, bal |-> b, val |-> v, aBal |-> NullBal ]
       IN /\ msgs'    = msgs \cup { ack }
          /\ aMaxBal' = [aMaxBal EXCEPT ![a] = b]
          /\ aAccBal' = [aAccBal EXCEPT ![a] = b]
          /\ aAccVal' = [aAccVal EXCEPT ![a] = v]
          /\ UNCHANGED decision

DecideFromAccepted ==
  /\ decision = NoVal
  /\ \E v \in Values, b \in Ballots :
       Quorum({ a \in Acceptors : aAccBal[a] = b /\ aAccVal[a] = v })
  /\ LET decm == [ type |-> "Decide",
                   from |-> CHOOSE x \in Agents : TRUE,
                   to   |-> "ALL",
                   bal  |-> NullBal,
                   val  |-> v,
                   aBal |-> NullBal ]
     IN /\ decm \notin msgs
        /\ msgs' = msgs \cup { decm }
        /\ decision' = v
        /\ UNCHANGED << aMaxBal, aAccBal, aAccVal >>

AdoptDecision ==
  \E m \in msgs :
    /\ decision = NoVal
    /\ m.type = "Decide"
    /\ m.val \in Values
    /\ decision' = m.val
    /\ UNCHANGED << msgs, aMaxBal, aAccBal, aAccVal >>

Next ==
    SendPrepare
  \/ Promise
  \/ SendAccept
  \/ AcceptAndAck
  \/ DecideFromAccepted
  \/ AdoptDecision

PaxosSpec == Init /\ [][Next]_vars

(*
  Safety: non-triviality — only proposed values can be learned.
*)
PaxosNontriviality == decision = NoVal \/ decision \in ProposedVals

(*
  Consistency over the decision variable:
  Once decision equals any concrete value v, it remains v forever.
*)
PaxosConsistency == \A v \in Values : [] (decision = v => [] (decision = v))

(*
  Explicitly no liveness: Paxos does not guarantee termination under the
  asynchronous fault model (FLP); we expose this as a named operator set to FALSE.
*)
Liveness == FALSE

=============================================================================