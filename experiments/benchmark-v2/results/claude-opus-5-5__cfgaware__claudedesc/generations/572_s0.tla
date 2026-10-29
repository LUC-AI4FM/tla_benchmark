---------------------------- MODULE AbstractCommitLogs ----------------------------
(***************************************************************************)
(* An abstract specification of a distributed consensus algorithm.        *)
(* Each node keeps a commit log, which is a sequence of terms. Logs are    *)
(* append-only and never diverge from one another.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Servers,    \* finite set of servers
          Terms,      \* strictly totally ordered set of terms
          StartTerm   \* the smallest term

ASSUME /\ IsFiniteSet(Servers)
       /\ Terms \subseteq Nat
       /\ StartTerm \in Terms
       /\ \A t \in Terms : StartTerm <= t

VARIABLE cLogs

vars == <<cLogs>>

---------------------------------------------------------------------------
(* Helpers *)

\* s is a prefix of t
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

\* Two sequences are prefix-comparable
Comparable(s, t) == IsPrefix(s, t) \/ IsPrefix(t, s)

\* Bound on the length of a single extension, so TLC can enumerate it.
MaxExtendLen == 2

\* All sequences of terms with length between 1 and MaxExtendLen.
ExtSeqs == UNION { [1..n -> Terms] : n \in 1..MaxExtendLen }

\* Whether every element of a sequence is a term
AllTerms(s) == \A k \in 1..Len(s) : s[k] \in Terms

\* Server i has a log of maximum length among all servers
IsMaxLen(i) == \A j \in Servers : Len(cLogs[i]) >= Len(cLogs[j])

---------------------------------------------------------------------------

TypeOK == cLogs \in [Servers -> Seq(Terms)]

InitLogs == { <<>>,
              <<StartTerm, StartTerm>>,
              <<StartTerm, StartTerm, StartTerm, StartTerm>> }

Init == cLogs \in [Servers -> InitLogs]

---------------------------------------------------------------------------
(* Actions *)

\* Node i appends a suffix of a longer log of node j onto its own log.
Copy(i) ==
    \E j \in Servers :
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
              cLogs' = [cLogs EXCEPT ![i] =
                          @ \o SubSeq(cLogs[j], Len(cLogs[i]) + 1, k)]

\* A node with the longest log appends a (nonempty, finite) sequence of terms.
Extend(i) ==
    /\ IsMaxLen(i)
    /\ \E s \in ExtSeqs :
          cLogs' = [cLogs EXCEPT ![i] = @ \o s]

\* Axiomatic formulation of Extend.
ExtendAxiom(i) ==
    /\ IsMaxLen(i)
    /\ DOMAIN cLogs' = Servers
    /\ \A j \in Servers \ {i} : cLogs'[j] = cLogs[j]
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ Len(cLogs'[i]) > Len(cLogs[i])
    /\ Len(cLogs'[i]) <= Len(cLogs[i]) + MaxExtendLen
    /\ AllTerms(cLogs'[i])

\* Node i copies a longest log from j and extends it, in one atomic step.
CopyMaxAndExtend(i) ==
    \E j \in Servers :
        /\ IsMaxLen(j)
        /\ \E s \in ExtSeqs :
              cLogs' = [cLogs EXCEPT ![i] = cLogs[j] \o s]

\* Axiomatic formulation of CopyMaxAndExtend.
CopyMaxAndExtendAxiom(i) ==
    \E j \in Servers :
        /\ IsMaxLen(j)
        /\ DOMAIN cLogs' = Servers
        /\ \A k \in Servers \ {i} : cLogs'[k] = cLogs[k]
        /\ IsPrefix(cLogs[j], cLogs'[i])
        /\ Len(cLogs'[i]) > Len(cLogs[j])
        /\ Len(cLogs'[i]) <= Len(cLogs[j]) + MaxExtendLen
        /\ AllTerms(cLogs'[i])

Next ==
    \E i \in Servers :
        \/ Copy(i)
        \/ Extend(i)
        \/ CopyMaxAndExtend(i)

AbsSpec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Properties *)

\* Logs only grow by prefix extension.
AppendOnlyProp ==
    [][\A i \in Servers : IsPrefix(cLogs[i], cLogs'[i])]_vars

\* Any two logs are prefix-comparable (no divergence).
NoConflicts ==
    \A i, j \in Servers : Comparable(cLogs[i], cLogs[j])

\* The action formulations are equivalent to their axiomatic versions.
EquivExtendProp ==
    [][\A i \in Servers : Extend(i) <=> ExtendAxiom(i)]_vars

EquivCopyMaxAndExtendProp ==
    [][\A i \in Servers : CopyMaxAndExtend(i) <=> CopyMaxAndExtendAxiom(i)]_vars

===============================================================================