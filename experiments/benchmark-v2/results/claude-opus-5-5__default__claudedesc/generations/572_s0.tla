---------------------------- MODULE AbstractConsensusLogs ----------------------------
(***************************************************************************)
(* Abstract distributed consensus: each server holds an append-only        *)
(* commit log (a sequence of terms), and logs never diverge.               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server,          \* finite set of servers
          Terms,           \* set of terms
          LessThan(_, _),  \* strict total order on Terms
          StartTerm        \* the smallest term

ASSUME ServerFinite == IsFiniteSet(Server)

ASSUME TermsOrder ==
    /\ StartTerm \in Terms
    \* Irreflexive
    /\ \A t \in Terms : ~LessThan(t, t)
    \* Transitive
    /\ \A t1, t2, t3 \in Terms :
          (LessThan(t1, t2) /\ LessThan(t2, t3)) => LessThan(t1, t3)
    \* Total
    /\ \A t1, t2 \in Terms :
          t1 # t2 => (LessThan(t1, t2) \/ LessThan(t2, t1))
    \* StartTerm is the smallest element
    /\ \A t \in Terms : t # StartTerm => LessThan(StartTerm, t)

VARIABLES cLogs   \* cLogs[s] is the commit log of server s

vars == <<cLogs>>

---------------------------------------------------------------------------
(* Helper operators *)

\* s is a prefix of t
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

\* Server i has a log of maximal length among all servers
IsMaxLog(i) == \A j \in Server : Len(cLogs[i]) >= Len(cLogs[j])

\* All servers other than i keep their log unchanged
OthersUnchanged(i) == \A j \in Server \ {i} : cLogs'[j] = cLogs[j]

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK == cLogs \in [Server -> Seq(Terms)]

---------------------------------------------------------------------------
(* Initial states *)

InitLogs ==
    { <<>>,
      <<StartTerm, StartTerm>>,
      <<StartTerm, StartTerm, StartTerm, StartTerm>> }

Init == cLogs \in [Server -> InitLogs]

---------------------------------------------------------------------------
(* Actions *)

\* Node i appends a suffix of a longer log held by node j.
Copy(i) ==
    \E j \in Server :
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
              cLogs' = [cLogs EXCEPT ![i] =
                          @ \o SubSeq(cLogs[j], Len(cLogs[i]) + 1, k)]

\* A node with a longest log appends an arbitrary finite sequence of terms.
Extend(i) ==
    /\ IsMaxLog(i)
    /\ \E s \in Seq(Terms) :
          cLogs' = [cLogs EXCEPT ![i] = @ \o s]

\* Axiomatic (equivalent) formulation of Extend.
ExtendAxiom(i) ==
    /\ IsMaxLog(i)
    /\ cLogs' \in [Server -> Seq(Terms)]
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ OthersUnchanged(i)

\* Node i copies a longest log (from j) and extends it in one atomic step.
CopyMaxAndExtend(i) ==
    \E j \in Server :
        /\ IsMaxLog(j)
        /\ \E s \in Seq(Terms) :
              cLogs' = [cLogs EXCEPT ![i] = cLogs[j] \o s]

\* Axiomatic (equivalent) formulation of CopyMaxAndExtend.
CopyMaxAndExtendAxiom(i) ==
    \E j \in Server :
        /\ IsMaxLog(j)
        /\ cLogs' \in [Server -> Seq(Terms)]
        /\ IsPrefix(cLogs[j], cLogs'[i])
        /\ OthersUnchanged(i)

---------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \E i \in Server :
        \/ Copy(i)
        \/ Extend(i)
        \/ CopyMaxAndExtend(i)

\* Version of Next using the axiomatic formulations (more efficient for TLC)
NextAxiom ==
    \E i \in Server :
        \/ Copy(i)
        \/ ExtendAxiom(i)
        \/ CopyMaxAndExtendAxiom(i)

AbsSpec == Init /\ [][Next]_vars

Spec == AbsSpec

---------------------------------------------------------------------------
(* Properties *)

\* Logs only grow by prefix extension.
AppendOnlyProp ==
    [][\A i \in Server : IsPrefix(cLogs[i], cLogs'[i])]_vars

\* Any two logs are prefix-comparable: logs never diverge.
NoConflicts ==
    \A i, j \in Server :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

\* Equivalence of action formulations with their axiomatic versions.
ExtendEquivalence ==
    [][\A i \in Server : Extend(i) <=> ExtendAxiom(i)]_vars

CopyMaxAndExtendEquivalence ==
    [][\A i \in Server : CopyMaxAndExtend(i) <=> CopyMaxAndExtendAxiom(i)]_vars

NextEquivalence ==
    [][Next <=> NextAxiom]_vars

---------------------------------------------------------------------------
THEOREM AbsSpec => []TypeOK
THEOREM AbsSpec => []NoConflicts
THEOREM AbsSpec => AppendOnlyProp
THEOREM AbsSpec => ExtendEquivalence
THEOREM AbsSpec => CopyMaxAndExtendEquivalence
=============================================================================