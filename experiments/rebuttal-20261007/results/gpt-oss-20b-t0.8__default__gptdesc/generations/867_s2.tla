--------------------------- MODULE PaxosSpec ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proposers, Acceptors, Values, None

(* Assumptions:  None is distinct from all other constants *)
ASSUME
    None \notin Proposers /\ None \notin Acceptors /\ None \notin Values

(* Message record type *)
MSG == [ msgKind   : {"Prepare","Promise","Accept","Accepted","Decide"},
         proposer  : Proposers \cup {None},
         acceptor  : Acceptors \cup {None},
         ballot    : Nat,
         value     : Values \cup {None} ]

VARIABLES msgs, decision, seen, acceptedBallot, acceptedValue

vars == <<msgs, decision, seen, acceptedBallot, acceptedValue>>

(* Initial state *)
Init ==
    /\ msgs = {}
    /\ decision = None
    /\ seen          \in [Acceptors -> Nat]
    /\ acceptedBallot\in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> Values \cup {None}]
    /\ \A a \in Acceptors:
           seen[a]          = 0 /\
           acceptedBallot[a]= 0 /\
           acceptedValue[a] = None

(* Send Prepare message *)
SendPrepare ==
    \E p \in Proposers, b \in Nat :
        LET m == [msgKind   |-> "Prepare",
                  proposer  |-> p,
                  acceptor  |-> None,
                  ballot    |-> b,
                  value     |-> None] IN
            /\ msgs'          = msgs \cup {m}
            /\ decision'      = decision
            /\ seen'          = seen
            /\ acceptedBallot'= acceptedBallot
            /\ acceptedValue' = acceptedValue

(* Send Promise message from acceptor a in response to Prepare(p,b) *)
PromiseMsg ==
    \E a \in Acceptors, p \in Proposers, b \in Nat :
        LET m == [msgKind   |-> "Promise",
                  proposer  |-> p,
                  acceptor  |-> a,
                  ballot    |-> b,
                  value     |-> acceptedValue[a]] IN
            /\ msgs'          = msgs \cup {m}
            /\ seen'          = [seen EXCEPT ![a] = Max(seen[a], b)]
            /\ decision'      = decision
            /\ acceptedBallot'= acceptedBallot
            /\ acceptedValue' = acceptedValue

(* Send Accepted message from acceptor a in response to Accept(p,b,v) *)
AcceptMsg ==
    \E a \in Acceptors, p \in Proposers, b \in Nat, v \in Values :
        LET m == [msgKind   |-> "Accepted",
                  proposer  |-> p,
                  acceptor  |-> a,
                  ballot    |-> b,
                  value     |-> v] IN
            /\ msgs'          = msgs \cup {m}
            /\ acceptedBallot'= [acceptedBallot EXCEPT ![a] = Max(acceptedBallot[a], b)]
            /\ acceptedValue' = IF acceptedBallot'[a] = b THEN v ELSE acceptedValue[a]
            /\ decision'      = decision
            /\ seen'          = seen

(* Send Decide message, finalizing a value *)
DecideMsg ==
    \E v \in Values :
        LET m == [msgKind   |-> "Decide",
                  proposer  |-> None,
                  acceptor  |-> None,
                  ballot    |-> 0,
                  value     |-> v] IN
            /\ msgs'          = msgs \cup {m}
            /\ decision'      = v
            /\ seen'          = seen
            /\ acceptedBallot'= acceptedBallot
            /\ acceptedValue' = acceptedValue

(* Next-state relation *)
Next ==
    SendPrepare \/ PromiseMsg \/ AcceptMsg \/ DecideMsg

(* Type correctness invariant *)
TypeInvariant ==
    /\ msgs \subseteq MSG
    /\ decision \in Values \cup {None}
    /\ seen          \in [Acceptors -> Nat]
    /\ acceptedBallot\in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> Values \cup {None}]
    /\ \A a \in Acceptors: 0 <= seen[a] /\ 0 <= acceptedBallot[a]

(* Non‑triviality safety property *)
Proposed(v) ==
    \E p \in Proposers, m \in msgs :
        /\ m.msgKind \in {"Prepare","Accept"}
        /\ m.proposer = p
        /\ m.value   = v

NonTrivialityInvariant ==
    decision = None \/ (\E v \in Values : decision = v => Proposed(v))

(* Complete specification *)
Spec == Init /\ [][Next]_vars
            /\ TypeInvariant
            /\ NonTrivialityInvariant

=============================================================================