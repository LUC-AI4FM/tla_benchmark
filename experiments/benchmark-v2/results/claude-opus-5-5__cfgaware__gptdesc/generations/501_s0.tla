---------------------------- MODULE MultiPaxos_MC ----------------------------
(***************************************************************************)
(* Model-checking wrapper around a MultiPaxos specification.  It adds a    *)
(* type invariant, a nontriviality invariant and a per-slot consistency    *)
(* invariant over the MultiPaxos state.  It also checks the learned        *)
(* values against an abstract multi-slot consensus interface              *)
(* (ConsensusMulti).                                                       *)
(*                                                                         *)
(* Checking the refinement to ConsensusMulti is only feasible on very      *)
(* small constant instances because of state-space blowup.  The simpler    *)
(* invariants can be checked on larger instances.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Replicas, Values, Slots, Ballots

ConstBallots == 0..2

SymmetricPerms == Permutations(Replicas) \cup Permutations(Values)

None == CHOOSE x : x \notin Values

NoBal == -1

Quorums == { Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas) }

VARIABLES msgs,     \* set of all messages ever sent
          maxBal,   \* maxBal[r]: highest ballot replica r has promised
          accBal,   \* accBal[r][s]: ballot of last vote by r in slot s
          accVal,   \* accVal[r][s]: value of last vote by r in slot s
          learned   \* learned[r][s]: value learned by r in slot s (or None)

vars == <<msgs, maxBal, accBal, accVal, learned>>

-----------------------------------------------------------------------------
(* Message types *)

VoteRec == [bal : Ballots \cup {NoBal}, val : Values \cup {None}]

Msg1a == [type : {"1a"}, bal : Ballots]
Msg1b == [type : {"1b"}, from : Replicas, bal : Ballots, votes : [Slots -> VoteRec]]
Msg2a == [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
Msg2b == [type : {"2b"}, from : Replicas, bal : Ballots, slot : Slots, val : Values]

Messages == Msg1a \cup Msg1b \cup Msg2a \cup Msg2b

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* MultiPaxos *)

Init ==
    /\ msgs = {}
    /\ maxBal = [r \in Replicas |-> NoBal]
    /\ accBal = [r \in Replicas |-> [s \in Slots |-> NoBal]]
    /\ accVal = [r \in Replicas |-> [s \in Slots |-> None]]
    /\ learned = [r \in Replicas |-> [s \in Slots |-> None]]

Phase1a(b) ==
    /\ ~ \E m \in msgs : m.type = "1a" /\ m.bal = b
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, accBal, accVal, learned>>

Phase1b(r) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[r]
        /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
        /\ Send([type  |-> "1b", from |-> r, bal |-> m.bal,
                 votes |-> [s \in Slots |-> [bal |-> accBal[r][s],
                                             val |-> accVal[r][s]]]])
        /\ UNCHANGED <<accBal, accVal, learned>>

SafeValue(b, s, Q, v) ==
    LET Q1b   == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.from \in Q}
        voted == {m \in Q1b : m.votes[s].bal # NoBal}
    IN  /\ \A q \in Q : \E m \in Q1b : m.from = q
        /\ \/ voted = {}
           \/ LET best == CHOOSE m \in voted :
                            \A m2 \in voted : m2.votes[s].bal =< m.votes[s].bal
              IN  v = best.votes[s].val

Phase2a(b, s, v) ==
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums : SafeValue(b, s, Q, v)
    /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, accBal, accVal, learned>>

Phase2b(r) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[r]
        /\ maxBal' = [maxBal EXCEPT ![r] = m.bal]
        /\ accBal' = [accBal EXCEPT ![r][m.slot] = m.bal]
        /\ accVal' = [accVal EXCEPT ![r][m.slot] = m.val]
        /\ Send([type |-> "2b", from |-> r, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED learned

Learn(r, s) ==
    /\ learned[r][s] = None
    /\ \E b \in Ballots, v \in Values, Q \in Quorums :
          /\ \A q \in Q : \E m \in msgs :
                /\ m.type = "2b" /\ m.from = q /\ m.bal = b
                /\ m.slot = s /\ m.val = v
          /\ learned' = [learned EXCEPT ![r][s] = v]
    /\ UNCHANGED <<msgs, maxBal, accBal, accVal>>

Next ==
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E r \in Replicas : Phase1b(r)
    \/ \E b \in Ballots, s \in Slots, v \in Values : Phase2a(b, s, v)
    \/ \E r \in Replicas : Phase2b(r)
    \/ \E r \in Replicas, s \in Slots : Learn(r, s)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ msgs \subseteq Messages
    /\ maxBal \in [Replicas -> Ballots \cup {NoBal}]
    /\ accBal \in [Replicas -> [Slots -> Ballots \cup {NoBal}]]
    /\ accVal \in [Replicas -> [Slots -> Values \cup {None}]]
    /\ learned \in [Replicas -> [Slots -> Values \cup {None}]]

-----------------------------------------------------------------------------
(* Consensus-oriented invariants *)

\* Only values that were actually proposed can be learned.
NontrivialityInv ==
    \A r \in Replicas, s \in Slots :
        learned[r][s] # None =>
            \E m \in msgs : m.type = "2a" /\ m.slot = s /\ m.val = learned[r][s]

\* No two replicas learn different values for the same slot.
ConsistencyInv ==
    \A r1, r2 \in Replicas, s \in Slots :
        (learned[r1][s] # None /\ learned[r2][s] # None)
            => learned[r1][s] = learned[r2][s]

-----------------------------------------------------------------------------
(* Abstract ConsensusMulti interface, instantiated via a refinement        *)
(* mapping from the learned values.                                        *)

chosenBar ==
    [s \in Slots |->
        IF \E r \in Replicas : learned[r][s] # None
        THEN learned[CHOOSE r \in Replicas : learned[r][s] # None][s]
        ELSE None]

CM_Init(chosen) == chosen = [s \in Slots |-> None]

CM_Next(chosen, chosenP) ==
    \E s \in Slots, v \in Values :
        /\ chosen[s] = None
        /\ chosenP = [chosen EXCEPT ![s] = v]

ConsensusMultiSpec ==
    /\ CM_Init(chosenBar)
    /\ [][CM_Next(chosenBar, chosenBar')]_chosenBar

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => ConsensusMultiSpec
THEOREM Spec => []NontrivialityInv
THEOREM Spec => []ConsistencyInv
=============================================================================