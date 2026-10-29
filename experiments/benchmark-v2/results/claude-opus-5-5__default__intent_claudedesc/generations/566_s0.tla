---- MODULE ReplicatedLog ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Server,      \* the set of servers in the cluster, e.g. {s1, s2, s3}
    MaxTerm,     \* largest term that may be used
    MaxLogLen    \* bound on log length, for model checking

ASSUME ServerAssumption  == Server # {} /\ IsFiniteSet(Server)
ASSUME MaxTermAssumption == MaxTerm \in Nat /\ MaxTerm >= 1
ASSUME MaxLogLenAssumption == MaxLogLen \in Nat /\ MaxLogLen >= 1

VARIABLES
    log          \* log[s] is the sequence of entry terms held by server s

vars == << log >>

----------------------------------------------------------------------------
(* Helper definitions *)

Terms == 1..MaxTerm

\* All sequences over set S of length at most n
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Raft-style "at least as up-to-date" comparison of two logs
IsUpToDate(xlog, ylog) ==
    \/ LastTerm(xlog) > LastTerm(ylog)
    \/ /\ LastTerm(xlog) = LastTerm(ylog)
       /\ Len(xlog) >= Len(ylog)

\* The longest common prefix length of two logs
CommonPrefixLen(xlog, ylog) ==
    LET n == IF Len(xlog) < Len(ylog) THEN Len(xlog) ELSE Len(ylog)
    IN  IF \E k \in 0..n : TRUE
        THEN CHOOSE k \in 0..n :
                /\ \A i \in 1..k : xlog[i] = ylog[i]
                /\ \/ k = n
                   \/ xlog[k+1] # ylog[k+1]
        ELSE 0

----------------------------------------------------------------------------
(* Initial state: every server starts with an empty log *)

Init ==
    log = [s \in Server |-> << >>]

----------------------------------------------------------------------------
(* Actions *)

\* Log extension: server s appends a new entry tagged with term t.
\* Terms in a log never decrease, reflecting monotone leadership epochs.
AppendEntry(s, t) ==
    /\ Len(log[s]) < MaxLogLen
    /\ t \in Terms
    /\ t >= LastTerm(log[s])
    /\ log' = [log EXCEPT ![s] = Append(@, t)]

\* Log convergence: server j adopts a (non-empty) prefix of a more
\* up-to-date server i's log, discarding any conflicting suffix of its own.
\* This abstracts away the details of replication / message passing.
ReplicateLog(i, j) ==
    /\ i # j
    /\ IsUpToDate(log[i], log[j])
    /\ log[i] # log[j]
    /\ \E k \in (CommonPrefixLen(log[i], log[j]) + 1)..Len(log[i]) :
          log' = [log EXCEPT ![j] = SubSeq(log[i], 1, k)]

\* A server may discard an uncommitted suffix of its log (e.g. on conflict).
TruncateLog(s) ==
    /\ Len(log[s]) > 0
    /\ \E k \in 0..(Len(log[s]) - 1) :
          log' = [log EXCEPT ![s] = SubSeq(log[s], 1, k)]

Next ==
    \/ \E s \in Server, t \in Terms : AppendEntry(s, t)
    \/ \E i, j \in Server : ReplicateLog(i, j)
    \/ \E s \in Server : TruncateLog(s)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Safety properties *)

\* Type safety: every log is a sequence of valid terms
TypeOK ==
    log \in [Server -> Seq(Terms)]

\* Bounded growth: no log exceeds the maximum length
BoundedLength ==
    \A s \in Server : Len(log[s]) <= MaxLogLen

\* Combined finite type invariant (useful for TLC)
TypeOKBounded ==
    log \in [Server -> BoundedSeq(Terms, MaxLogLen)]

\* Terms within each log are monotonically non-decreasing
TermsMonotonic ==
    \A s \in Server :
        \A i, j \in 1..Len(log[s]) : i <= j => log[s][i] <= log[s][j]

Invariants ==
    /\ TypeOK
    /\ BoundedLength
    /\ TypeOKBounded
    /\ TermsMonotonic

----------------------------------------------------------------------------
(* Model checking support *)

\* State constraint bounding log growth
StateConstraint ==
    \A s \in Server : Len(log[s]) <= MaxLogLen

\* Symmetry reduction: servers are interchangeable
Symmetry == Permutations(Server)

THEOREM Spec => [](TypeOK /\ BoundedLength /\ TermsMonotonic)

====