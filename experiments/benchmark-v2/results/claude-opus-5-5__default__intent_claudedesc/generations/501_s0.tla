------------------------------ MODULE MultiPaxos ------------------------------
(***************************************************************************)
(* Multi-Paxos consensus over a finite set of slots.  Every replica acts  *)
(* as both proposer and acceptor.                                          *)
(*                                                                         *)
(* A single Phase 1 (prepare) for ballot b covers all slots.  Each 1b      *)
(* reply reports the highest-ballot vote the acceptor has cast in every    *)
(* slot.  Phase 2 (accept) then runs separately for each slot within      *)
(* ballot b.                                                               *)
(*                                                                         *)
(* The spec refines an abstract multi-slot consensus specification that    *)
(* is defined inline below (AbsSpec).                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Replicas,   \* set of replicas (proposers + acceptors)
          Values,     \* set of proposable values
          Slots,      \* set of consensus instances (log positions)
          MaxBallot   \* largest ballot number (for bounded model checking)

ASSUME /\ IsFiniteSet(Replicas) /\ Replicas # {}
       /\ IsFiniteSet(Slots)
       /\ MaxBallot \in Nat

Ballots == 0..MaxBallot

None == CHOOSE v : v \notin Values

\* Majority quorums: any two of them intersect.
Quorums == {Q \in SUBSET Replicas : 2 * Cardinality(Q) > Cardinality(Replicas)}

VARIABLES
    proposed,  \* proposed[s] : set of values proposed for slot s
    maxBal,    \* maxBal[r]   : highest ballot replica r has promised/joined
    maxVBal,   \* maxVBal[r][s] : ballot of r's latest vote in slot s (-1 = none)
    maxVal,    \* maxVal[r][s]  : value of r's latest vote in slot s (None = none)
    msgs,      \* set of all messages sent so far
    learned    \* learned[s] : set of values learned for slot s

vars == <<proposed, maxBal, maxVBal, maxVal, msgs, learned>>

-----------------------------------------------------------------------------
Messages ==
       [type : {"1a"}, bal : Ballots, from : Replicas]
  \cup [type : {"1b"}, bal : Ballots, acc : Replicas,
        mbal : [Slots -> Ballots \cup {-1}],
        mval : [Slots -> Values \cup {None}]]
  \cup [type : {"2a"}, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, slot : Slots, val : Values, acc : Replicas]

TypeOK ==
  /\ proposed \in [Slots -> SUBSET Values]
  /\ maxBal   \in [Replicas -> Ballots \cup {-1}]
  /\ maxVBal  \in [Replicas -> [Slots -> Ballots \cup {-1}]]
  /\ maxVal   \in [Replicas -> [Slots -> Values \cup {None}]]
  /\ msgs     \subseteq Messages
  /\ learned  \in [Slots -> SUBSET Values]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
  /\ proposed = [s \in Slots |-> {}]
  /\ maxBal   = [r \in Replicas |-> -1]
  /\ maxVBal  = [r \in Replicas |-> [s \in Slots |-> -1]]
  /\ maxVal   = [r \in Replicas |-> [s \in Slots |-> None]]
  /\ msgs     = {}
  /\ learned  = [s \in Slots |-> {}]

\* A client proposes value v for slot s.
Propose(v, s) ==
  /\ v \notin proposed[s]
  /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, learned>>

\* Replica r starts ballot b by sending a prepare request.
Phase1a(r, b) ==
  /\ ~\E m \in msgs : m.type = "1a" /\ m.bal = b
  /\ Send([type |-> "1a", bal |-> b, from |-> r])
  /\ UNCHANGED <<proposed, maxBal, maxVBal, maxVal, learned>>

\* Acceptor a promises ballot m.bal.  Its reply reports its latest
\* vote in every slot.
Phase1b(a) ==
  \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", bal |-> m.bal, acc |-> a,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<proposed, maxVBal, maxVal, learned>>

\* After a quorum of 1b replies for ballot b, propose a value for slot s.
\* The value must be the one voted for with the highest ballot in s if
\* such a vote exists.  Otherwise it may be any value proposed for s.
Phase2a(b, s) ==
  /\ ~\E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
           Q1bv == {m \in Q1b : m.mbal[s] >= 0}
       IN /\ \A a \in Q : \E m \in Q1b : m.acc = a
          /\ \E v \in Values :
               /\ \/ /\ Q1bv = {}
                     /\ v \in proposed[s]
                  \/ \E m \in Q1bv :
                       /\ m.mval[s] = v
                       /\ \A mm \in Q1bv : m.mbal[s] >= mm.mbal[s]
               /\ Send([type |-> "2a", bal |-> b, slot |-> s, val |-> v])
  /\ UNCHANGED <<proposed, maxBal, maxVBal, maxVal, learned>>

\* Acceptor a accepts a 2a message.
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
    /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
    /\ maxVal'  = [maxVal  EXCEPT ![a][m.slot] = m.val]
    /\ Send([type |-> "2b", bal |-> m.bal, slot |-> m.slot,
             val |-> m.val, acc |-> a])
    /\ UNCHANGED <<proposed, learned>>

\* Value v is learned for slot s once a quorum has accepted it in one ballot.
Learn(s, v) ==
  /\ \E b \in Ballots, Q \in Quorums :
       \A a \in Q : \E m \in msgs :
          /\ m.type = "2b" /\ m.bal = b /\ m.slot = s
          /\ m.val = v /\ m.acc = a
  /\ learned' = [learned EXCEPT ![s] = @ \cup {v}]
  /\ UNCHANGED <<proposed, maxBal, maxVBal, maxVal, msgs>>

Next ==
  \/ \E v \in Values, s \in Slots : Propose(v, s)
  \/ \E r \in Replicas, b \in Ballots : Phase1a(r, b)
  \/ \E a \in Replicas : Phase1b(a)
  \/ \E b \in Ballots, s \in Slots : Phase2a(b, s)
  \/ \E a \in Replicas : Phase2b(a)
  \/ \E s \in Slots, v \in Values : Learn(s, v)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Nontriviality: a learned value must have been proposed for that slot.
Nontriviality == \A s \in Slots : learned[s] \subseteq proposed[s]

\* Consistency: at most one value is learned per slot.
Consistency == \A s \in Slots : Cardinality(learned[s]) <= 1

\* Stability: once learned, a value stays learned forever.
Stability ==
  \A s \in Slots, v \in Values : [](v \in learned[s] => [](v \in learned[s]))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract multi-slot consensus specification, refined by MultiPaxos.     *)
(***************************************************************************)
AbsVars == <<proposed, learned>>

AbsInit ==
  /\ proposed = [s \in Slots |-> {}]
  /\ learned  = [s \in Slots |-> {}]

AbsPropose ==
  \E s \in Slots, v \in Values :
    /\ proposed' = [proposed EXCEPT ![s] = @ \cup {v}]
    /\ UNCHANGED learned

AbsLearn ==
  \E s \in Slots, v \in Values :
    /\ learned[s] = {}
    /\ v \in proposed[s]
    /\ learned' = [learned EXCEPT ![s] = {v}]
    /\ UNCHANGED proposed

AbsNext == AbsPropose \/ AbsLearn

AbsSpec == AbsInit /\ [][AbsNext]_AbsVars

\* MultiPaxos implements abstract consensus: Spec => AbsSpec.
Refinement == AbsSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Symmetry for TLC model checking.                                        *)
(***************************************************************************)
Symmetry == Permutations(Replicas) \cup Permutations(Values) \cup Permutations(Slots)

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
THEOREM Spec => Stability
THEOREM Spec => Refinement
=============================================================================