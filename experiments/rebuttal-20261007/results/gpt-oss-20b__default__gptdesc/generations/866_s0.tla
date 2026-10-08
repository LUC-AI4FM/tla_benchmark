MODULE FastPaxos
EXTENDS Naturals, Sequences, TLC, Integers

CONSTANTS Agents, Values, COORDINATOR

ASSUME
  Agents /= {}
  Values /= {}
  COORDINATOR ∈ Agents

VARIABLES round, phase, proposals, decided, fastVotes, classicPromises

(* Type invariants *)
TypeInv ==
  /\ round ∈ Nat
  /\ phase ∈ {"fast","classic"}
  /\ proposals ∈ [Agents -> (Values ∪ {⊥})]
  /\ decided ∈ [Agents -> (Values ∪ {⊥})]
  /\ fastVotes ∈ [Agents -> (Values ∪ {⊥})]
  /\ classicPromises ∈ [Agents -> (Values ∪ {⊥})]

Majority == Floor[#Agents / 2] + 1

Init ==
  /\ round = 0
  /\ phase = "fast"
  /\ proposals = [a \in Agents |-> ⊥]
  /\ decided = [a \in Agents |-> ⊥]
  /\ fastVotes = [a \in Agents |-> ⊥]
  /\ classicPromises = [a \in Agents |-> ⊥]

Propose(a, v) ==
  /\ a ∈ Agents
  /\ v ∈ Values
  /\ proposals[a] = ⊥
  /\ proposals' = [proposals EXCEPT ![a] = v]
  /\ UNCHANGED <<round, phase, decided, fastVotes, classicPromises>>

FastRoundStart ==
  /\ COORDINATOR ∈ Agents
  /\ phase = "fast"
  /\ round' = round + 1
  /\ fastVotes' = [a \in Agents |-> ⊥]
  /\ UNCHANGED <<proposals, decided, phase, classicPromises>>

AgentSendFastVote(a) ==
  /\ a ∈ Agents
  /\ proposals[a] # ⊥
  /\ fastVotes[a] = ⊥
  /\ fastVotes' = [fastVotes EXCEPT ![a] = proposals[a]]
  /\ UNCHANGED <<round, phase, proposals, decided, classicPromises>>

CollectFast ==
  /\ phase = "fast"
  /\ Let votedVals == {fastVotes[a] : a ∈ Agents | fastVotes[a] # ⊥} IN
     /\ #{a \in Agents : fastVotes[a] # ⊥} >= Majority
     /\ IF #votedVals = 1 THEN
          LET v == CHOOSE x \in votedVals : TRUE IN
            /\ decided' = [decided EXCEPT ![a] = v | a ∈ Agents]
            /\ UNCHANGED <<round, phase, proposals, fastVotes, classicPromises>>
        ELSE
          /\ phase' = "classic"
          /\ classicPromises' = [a \in Agents |-> ⊥]
          /\ UNCHANGED <<round, proposals, decided, fastVotes>>

ClassicRoundStart ==
  /\ COORDINATOR ∈ Agents
  /\ phase = "classic"
  /\ classicPromises' = [a \in Agents |-> ⊥]
  /\ UNCHANGED <<round, phase, proposals, decided, fastVotes>>

AgentSendPromise(a) ==
  /\ a ∈ Agents
  /\ phase = "classic"
  /\ classicPromises[a] = ⊥
  /\ classicPromises' = [classicPromises EXCEPT ![a] = proposals[a]]
  /\ UNCHANGED <<round, phase, proposals, decided, fastVotes>>

CollectClassic ==
  /\ phase = "classic"
  /\ Let promisedVals == {classicPromises[a] : a ∈ Agents | classicPromises[a] # ⊥} IN
     /\ #{a \in Agents : classicPromises[a] # ⊥} >= Majority
     /\ LET v == CHOOSE x \in promisedVals : TRUE IN
          /\ decided' = [decided EXCEPT ![a] = v | a ∈ Agents]
          /\ UNCHANGED <<round, phase, proposals, fastVotes, classicPromises>>

Next ==
  \/ ∃ a ∈ Agents, v ∈ Values : Propose(a,v)
  \/ FastRoundStart
  \/ ∃ a ∈ Agents : AgentSendFastVote(a)
  \/ CollectFast
  \/ ClassicRoundStart
  \/ ∃ a ∈ Agents : AgentSendPromise(a)
  \/ CollectClassic

Spec ==
  Init /\ [][Next]_<<round, phase, proposals, decided, fastVotes, classicPromises>> /\ TypeInv

NonTriviality ==
  ∀ a ∈ Agents :
    (decided[a] # ⊥) => (∃ b ∈ Agents : proposals[b] = decided[a])

Agreement ==
  ∀ a,b ∈ Agents :
    (decided[a] # ⊥ /\ decided[b] # ⊥) => decided[a] = decided[b]

Safety == NonTriviality /\ Agreement

ConsensusLiveness ==
  []<>(∀ a ∈ Agents : decided[a] # ⊥)

Fairness ==
  WF_∃(Propose)

============================================================================