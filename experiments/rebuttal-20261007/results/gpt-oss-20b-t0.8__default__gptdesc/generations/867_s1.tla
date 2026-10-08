MODULE Paxos
EXTENDS TLA+, Naturals

CONSTANTS Proposers, Acceptors, Values, None

VARIABLES msgs, HBS, HBA, HAV, Decided

IsPrepare(m) == m.kind = "Prepare"
IsPromise(m)  == m.kind = "Promise"
IsAcceptMsg(m)== m.kind = "Accept"
IsAccepted(m) == m.kind = "Accepted"
IsDecide(m)   == m.kind = "Decide"

SendPrepare(p,b) ==
  /\ p ∈ Proposers
  /\ b ∈ Nat
  /\ msgs' = msgs ∪ { [kind |-> "Prepare", proposer |-> p, ballot |-> b] }
  /\ UNCHANGED <<HBS,HBA,HAV,Decided>>

SendPromise(a,m) ==
  /\ a ∈ Acceptors
  /\ m ∈ msgs
  /\ IsPrepare(m)
  /\ msgs' = msgs ∪ { [kind |-> "Promise", acceptor |-> a,
                      ballot |-> m.ballot,
                      prevBallot |-> HBA[a],
                      prevValue |-> HAV[a]] }
  /\ HBS' = [HBS EXCEPT ![a] = IF HBS[a] >= m.ballot THEN HBS[a] ELSE m.ballot]
  /\ UNCHANGED <<HBA,HAV,Decided>>

SendAccept(p,b,v) ==
  /\ p ∈ Proposers
  /\ b ∈ Nat
  /\ v ∈ Values
  /\ msgs' = msgs ∪ { [kind |-> "Accept", proposer |-> p,
                      ballot |-> b, value |-> v] }
  /\ UNCHANGED <<HBS,HBA,HAV,Decided>>

SendAccepted(a,m) ==
  /\ a ∈ Acceptors
  /\ m ∈ msgs
  /\ IsAcceptMsg(m)
  /\ msgs' = msgs ∪ { [kind |-> "Accepted", acceptor |-> a,
                      ballot |-> m.ballot, value |-> m.value] }
  /\ HBS' = [HBS EXCEPT ![a] = IF HBS[a] >= m.ballot THEN HBS[a] ELSE m.ballot]
  /\ HBA' = [HBA EXCEPT ![a] = m.ballot]
  /\ HAV' = [HAV EXCEPT ![a] = m.value]
  /\ UNCHANGED Decided

SendDecide(v) ==
  /\ v ∈ Values
  /\ msgs' = msgs ∪ { [kind |-> "Decide", value |-> v] }
  /\ Decided' = v
  /\ UNCHANGED <<HBS,HBA,HAV>>

Next ==
  \/ ∃ p ∈ Proposers, b ∈ Nat : SendPrepare(p,b)
  \/ ∃ a ∈ Acceptors, m ∈ msgs : SendPromise(a,m)
  \/ ∃ p ∈ Proposers, b ∈ Nat, v ∈ Values : SendAccept(p,b,v)
  \/ ∃ a ∈ Acceptors, m ∈ msgs : SendAccepted(a,m)
  \/ ∃ v ∈ Values : SendDecide(v)

Init ==
  /\ msgs = {}
  /\ Decided = None
  /\ HBS \in [Acceptors -> Nat]
  /\ HBA \in [Acceptors -> Nat]
  /\ HAV \in [Acceptors -> (Values ∪ {None})]
  /\ ∀ a ∈ Acceptors : HBS[a] = 0 /\ HBA[a] = 0 /\ HAV[a] = None

vars == <<msgs, HBS, HBA, HAV, Decided>>

Spec == Init /\ [][Next]_vars

Safety ==
  /\ Decided # None => Decided ∈ Values
  /\ ∀ a ∈ Acceptors : HBA[a] <= HBS[a]
  /\ ∀ a ∈ Acceptors : IF HAV[a] = None THEN TRUE ELSE HAV[a] ∈ Values

Liveness == FALSE

(**** End of module ****)