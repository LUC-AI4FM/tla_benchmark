------------------------------ MODULE MCRaftAbstraction ------------------------------
(***************************************************************************)
(* Model-checking wrapper around a Raft-style log/term abstraction.        *)
(* This module restricts the server set, term range and log lengths so     *)
(* that state-space exploration is finite. It provides configuration-style *)
(* helper operators (server set, term bounds, bounded sequences, state     *)
(* constraints, symmetry set) together with the underlying abstraction so  *)
(* that the module is self-contained and parses with SANY.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, n3,   \* Three concrete (symmetric) server model values
          MaxLogLen     \* Upper bound on the length of any server's log

ASSUME MaxLogLen \in Nat

-----------------------------------------------------------------------------
(* Configuration-style helper operators                                    *)
-----------------------------------------------------------------------------

\* Concrete symmetric server set of three nodes.
MCServer == {n1, n2, n3}
Server == MCServer

\* Bounded term range.
MCTerms == 2..4

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Start term is the minimum of the term range.
MCStartTerm == Min(MCTerms)
MCMaxTerm   == Max(MCTerms)

\* All sequences over S with length at most n.
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

\* Log entries are terms; logs are bounded sequences of terms.
MCLogs == BoundedSeq(MCTerms, MaxLogLen)

\* Symmetry reduction through permutations of the server set.
MCSymmetry == Permutations(MCServer)

Quorums == { Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server) }

-----------------------------------------------------------------------------
(* Underlying abstraction                                                  *)
-----------------------------------------------------------------------------

VARIABLES currentTerm, state, log

vars == <<currentTerm, state, log>>

Leader   == "Leader"
Follower == "Follower"

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Server i's log is at least as up to date as server j's log.
IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ Len(log[i]) >= Len(log[j])

TypeOK ==
    /\ currentTerm \in [Server -> MCTerms]
    /\ state \in [Server -> {Leader, Follower}]
    /\ log \in [Server -> MCLogs]

Init ==
    /\ currentTerm = [s \in Server |-> MCStartTerm]
    /\ state = [s \in Server |-> Follower]
    /\ log = [s \in Server |-> <<>>]

\* Server i becomes leader in a new term with the votes of quorum Q.
BecomeLeader(i, Q) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in Q
    /\ newTerm <= MCMaxTerm
    /\ \A v \in Q : /\ currentTerm[v] < newTerm
                    /\ IsUpToDate(i, v)
    /\ currentTerm' = [s \in Server |-> IF s \in Q THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Leader
                    ELSE IF s \in Q THEN Follower
                    ELSE state[s]]
    /\ UNCHANGED log

\* A leader appends a new entry in its current term.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state>>

\* Follower i copies the next entry from server j's log.
GetEntries(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ Len(log[i]) < Len(log[j])
    /\ Len(log[i]) < MaxLogLen
    /\ \/ Len(log[i]) = 0
       \/ log[i][Len(log[i])] = log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state>>

\* Server i rolls back a divergent last entry, as observed from server j.
RollbackEntries(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ Len(log[i]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \/ log[i][Len(log[i])] # log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<currentTerm, state>>

\* Server i learns a newer term from server j and steps down.
UpdateTerms(i, j) ==
    /\ currentTerm[i] < currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED log

Next ==
    \/ \E i \in Server, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i, j \in Server : GetEntries(i, j)
    \/ \E i, j \in Server : RollbackEntries(i, j)
    \/ \E i, j \in Server : UpdateTerms(i, j)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Model-checking constraints                                              *)
-----------------------------------------------------------------------------

\* Explicit log length constraint.
LogLenConstraint == \A s \in Server : Len(log[s]) <= MaxLogLen

\* Terms stay within the bounded range.
TermConstraint == \A s \in Server : currentTerm[s] \in MCTerms

StateConstraint == LogLenConstraint /\ TermConstraint

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)
-----------------------------------------------------------------------------

OnePrimaryPerTerm ==
    \A s, t \in Server :
        (/\ state[s] = Leader
         /\ state[t] = Leader
         /\ currentTerm[s] = currentTerm[t]) => s = t

LogMatching ==
    \A s, t \in Server :
        \A k \in 1..Len(log[s]) :
            (/\ k <= Len(log[t])
             /\ log[s][k] = log[t][k])
                => SubSeq(log[s], 1, k) = SubSeq(log[t], 1, k)

TermsMonotonicInLog ==
    \A s \in Server :
        \A k \in 1..Len(log[s]) :
            k > 1 => log[s][k - 1] <= log[s][k]

THEOREM Spec => [](TypeOK /\ OnePrimaryPerTerm)

=============================================================================