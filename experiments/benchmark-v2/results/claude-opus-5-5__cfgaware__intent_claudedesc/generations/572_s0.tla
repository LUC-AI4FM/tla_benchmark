------------------------------ MODULE AbstractConsensus ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Servers, Terms, StartTerm

VARIABLES cLogs

vars == <<cLogs>>

ASSUME /\ Servers # {}
       /\ IsFiniteSet(Servers)
       /\ Terms \subseteq Nat
       /\ IsFiniteSet(Terms)
       /\ StartTerm \in Terms
       /\ \A t \in Terms : StartTerm <= t

-----------------------------------------------------------------------------
(* Helpers *)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

MaxLen == Cardinality(Terms)

\* All sequences over Terms with length in 1..n.
NonEmptySeqsUpTo(n) == UNION {[1..k -> Terms] : k \in 1..n}

\* All sequences over Terms with length in 0..n.
SeqsUpTo(n) == UNION {[1..k -> Terms] : k \in 0..n}

IsNonDecreasing(seq) ==
    \A i, j \in 1..Len(seq) : i <= j => seq[i] <= seq[j]

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

IsConsistent(s, t) == IsPrefix(s, t) \/ IsPrefix(t, s)

LastTerm(log) == IF Len(log) = 0 THEN StartTerm ELSE log[Len(log)]

MaxLogLength == Max({Len(cLogs[s]) : s \in Servers})

IsLongestLog(s) == Len(cLogs[s]) = MaxLogLength

\* Candidate new entries to append after the given log: non-empty and
\* with terms that never go below the term of the last entry.
NewEntries(log) ==
    { e \in NonEmptySeqsUpTo(MaxLen) :
        /\ IsNonDecreasing(e)
        /\ e[1] >= LastTerm(log) }

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ cLogs \in [Servers -> Seq(Terms)]

-----------------------------------------------------------------------------
(* Initial state: logs may be non-empty but must be mutually consistent *)

Init ==
    \E base \in SeqsUpTo(MaxLen) :
        /\ IsNonDecreasing(base)
        /\ \E lens \in [Servers -> 0..Len(base)] :
              cLogs = [s \in Servers |-> SubSeq(base, 1, lens[s])]

-----------------------------------------------------------------------------
(* Actions *)

\* A server with a longest log extends its own log.
Extend(s) ==
    /\ IsLongestLog(s)
    /\ \E e \in NewEntries(cLogs[s]) :
          cLogs' = [cLogs EXCEPT ![s] = cLogs[s] \o e]

\* A server copies a suffix from any server with a longer log.
Copy(s) ==
    \E t \in Servers :
        /\ Len(cLogs[t]) > Len(cLogs[s])
        /\ \E k \in (Len(cLogs[s]) + 1)..Len(cLogs[t]) :
              cLogs' = [cLogs EXCEPT ![s] = SubSeq(cLogs[t], 1, k)]

\* A server copies from a longest log and then extends further, atomically.
CopyMaxAndExtend(s) ==
    \E t \in Servers :
        /\ IsLongestLog(t)
        /\ \E e \in NewEntries(cLogs[t]) :
              cLogs' = [cLogs EXCEPT ![s] = cLogs[t] \o e]

Next ==
    \E s \in Servers :
        \/ Extend(s)
        \/ Copy(s)
        \/ CopyMaxAndExtend(s)

AbsSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Correctness properties *)

NoConflicts ==
    \A s, t \in Servers : IsConsistent(cLogs[s], cLogs[t])

AppendOnlyProp ==
    [][\A s \in Servers : IsPrefix(cLogs[s], cLogs'[s])]_vars

\* Extend is equivalent to CopyMaxAndExtend when the server already holds
\* a longest log (copying from itself).
EquivExtendProp ==
    [][\A s \in Servers :
          IsLongestLog(s) => (Extend(s) <=> (\E e \in NewEntries(cLogs[s]) :
                                  cLogs' = [cLogs EXCEPT ![s] = cLogs[s] \o e]))]_vars

\* CopyMaxAndExtend is equivalent to a copy of a longest log followed by an
\* extension: the new log of s strictly extends some longest log, and all
\* other servers are unchanged.
EquivCopyMaxAndExtendProp ==
    [][\A s \in Servers :
          CopyMaxAndExtend(s) =>
             /\ \E t \in Servers :
                   /\ IsLongestLog(t)
                   /\ IsPrefix(cLogs[t], cLogs'[s])
                   /\ Len(cLogs'[s]) > Len(cLogs[t])
             /\ \A u \in Servers \ {s} : cLogs'[u] = cLogs[u]]_vars

=============================================================================