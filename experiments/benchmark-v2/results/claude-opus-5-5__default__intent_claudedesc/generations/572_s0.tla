------------------------------ MODULE AbstractConsensusLog ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Server,      \* finite, fixed set of servers
    Terms,       \* totally ordered set of terms (subset of Nat)
    MaxLogLen    \* bound on log length (for finite model checking)

ASSUME ServerAssumption == IsFiniteSet(Server) /\ Server # {}
ASSUME TermsAssumption  == Terms \subseteq Nat /\ Terms # {}
ASSUME LenAssumption    == MaxLogLen \in Nat

VARIABLES clog   \* clog[s] is the commit log of server s: a sequence of terms

vars == << clog >>

----------------------------------------------------------------------------------------
\* Helper definitions

MinTerm == CHOOSE t \in Terms : \A u \in Terms : t <= u

\* Sequences over S with length between lo and hi
SeqsOfLen(S, lo, hi) == UNION { [1..k -> S] : k \in lo..hi }

\* Log l1 is a prefix of log l2
IsPrefix(l1, l2) ==
    /\ Len(l1) <= Len(l2)
    /\ \A k \in 1..Len(l1) : l1[k] = l2[k]

\* Two logs are consistent iff one is a prefix of the other
Consistent(l1, l2) == IsPrefix(l1, l2) \/ IsPrefix(l2, l1)

LastTerm(l) == IF l = << >> THEN MinTerm ELSE l[Len(l)]

\* Terms in a log are non-decreasing
TermsMonotone(l) == \A k \in 1..(Len(l) - 1) : l[k] <= l[k + 1]

\* Server s currently has a longest (or tied for longest) log
IsLongest(s) == \A t \in Server : Len(clog[t]) <= Len(clog[s])

\* Possible nonempty extensions of base: entries whose terms do not go backwards,
\* keeping the total length within MaxLogLen
Extensions(base) ==
    { e \in SeqsOfLen(Terms, 1, MaxLogLen - Len(base)) :
        /\ TermsMonotone(e)
        /\ e[1] >= LastTerm(base) }

\* Nonempty suffixes of src beyond the length of dst (dst must be a prefix of src)
CopySuffixes(dst, src) ==
    { SubSeq(src, Len(dst) + 1, k) : k \in (Len(dst) + 1)..Len(src) }

----------------------------------------------------------------------------------------
\* Initial state: logs may be non-empty but are all prefixes of a common log,
\* hence pairwise consistent.

Init ==
    \E L \in SeqsOfLen(Terms, 0, MaxLogLen) :
        /\ TermsMonotone(L)
        /\ clog \in [Server -> { SubSeq(L, 1, k) : k \in 0..Len(L) }]

TypeOK ==
    clog \in [Server -> SeqsOfLen(Terms, 0, MaxLogLen)]

----------------------------------------------------------------------------------------
\* Actions

\* A server with a longest log appends new entries (leader commits new entries).
ExtendLog(s) ==
    /\ IsLongest(s)
    /\ \E e \in Extensions(clog[s]) :
         clog' = [clog EXCEPT ![s] = clog[s] \o e]

\* A server with a shorter log copies a suffix from a server with a longer log.
CopyLog(s, t) ==
    /\ Len(clog[s]) < Len(clog[t])
    /\ \E suf \in CopySuffixes(clog[s], clog[t]) :
         clog' = [clog EXCEPT ![s] = clog[s] \o suf]

\* A server atomically copies a longest log and then extends it further.
CopyAndExtend(s, t) ==
    /\ IsLongest(t)
    /\ Len(clog[s]) < Len(clog[t])
    /\ \E e \in Extensions(clog[t]) :
         clog' = [clog EXCEPT ![s] = clog[s]
                                     \o SubSeq(clog[t], Len(clog[s]) + 1, Len(clog[t]))
                                     \o e]

Next ==
    \/ \E s \in Server : ExtendLog(s)
    \/ \E s, t \in Server : CopyLog(s, t)
    \/ \E s, t \in Server : CopyAndExtend(s, t)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------------------
\* Correctness properties

\* No conflicts: any two servers' logs are consistent (one is a prefix of the other).
NoConflicts ==
    \A s, t \in Server : Consistent(clog[s], clog[t])

\* Append-only: each server's log only grows; existing entries are never changed.
AppendOnlyStep ==
    \A s \in Server : IsPrefix(clog[s], clog'[s])

AppendOnly == [][AppendOnlyStep]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []NoConflicts
THEOREM Spec => AppendOnly
========================================================================================