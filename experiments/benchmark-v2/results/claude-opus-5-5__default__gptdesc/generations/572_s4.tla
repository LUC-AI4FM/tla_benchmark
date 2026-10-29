---------------------------- MODULE CommitLogs ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server,      \* finite set of servers
          Value,       \* finite set of log entry values
          MaxLogLen    \* bound on log length, used only by the TLC state constraint

ASSUME /\ IsFiniteSet(Server)
       /\ Server # {}
       /\ MaxLogLen \in Nat

VARIABLE cLogs

vars == <<cLogs>>

---------------------------------------------------------------------------
(* Helper operators *)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

MaxLen == Max({Len(cLogs[s]) : s \in Server})

IsLongest(i) == Len(cLogs[i]) = MaxLen

LongestLogs == {cLogs[s] : s \in {t \in Server : IsLongest(t)}}

Unchanged(i) == \A j \in Server \ {i} : cLogs'[j] = cLogs[j]

---------------------------------------------------------------------------
(* Type invariant and initial state *)

TypeOK == cLogs \in [Server -> Seq(Value)]

Init == cLogs = [s \in Server |-> << >>]

---------------------------------------------------------------------------
(* Existential (constructive) action definitions *)

\* Server i copies a nonempty suffix of server j's log, which extends its own.
CopySuffix(i, j) ==
    /\ IsPrefix(cLogs[i], cLogs[j])
    /\ Len(cLogs[j]) > Len(cLogs[i])
    /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
          cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, k)]

\* Server i holds a longest log and appends a new value to it.
ExtendLongestLog(i, v) ==
    /\ IsLongest(i)
    /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], v)]

\* Server i copies the longest log of server j and extends it with v.
CopyLongestAndExtend(i, j, v) ==
    /\ IsLongest(j)
    /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], v)]

Next ==
    \/ \E i, j \in Server : CopySuffix(i, j)
    \/ \E i \in Server, v \in Value : ExtendLongestLog(i, v)
    \/ \E i, j \in Server, v \in Value : CopyLongestAndExtend(i, j, v)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Axiom-style formulations (constraints on primed state), efficient for *)
(* refinement checking in TLC.                                           *)

CopySuffixAxiom(i) ==
    /\ Unchanged(i)
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ Len(cLogs'[i]) > Len(cLogs[i])
    /\ \E j \in Server : IsPrefix(cLogs'[i], cLogs[j])

ExtendLongestLogAxiom(i) ==
    /\ Unchanged(i)
    /\ IsLongest(i)
    /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ cLogs'[i][Len(cLogs'[i])] \in Value

CopyLongestAndExtendAxiom(i) ==
    /\ Unchanged(i)
    /\ Len(cLogs'[i]) = MaxLen + 1
    /\ SubSeq(cLogs'[i], 1, MaxLen) \in LongestLogs
    /\ cLogs'[i][Len(cLogs'[i])] \in Value

NextAxiom ==
    \E i \in Server :
        /\ cLogs'[i] \in Seq(Value)
        /\ \/ CopySuffixAxiom(i)
           \/ ExtendLongestLogAxiom(i)
           \/ CopyLongestAndExtendAxiom(i)

SpecAxiom == Init /\ [][NextAxiom]_vars

---------------------------------------------------------------------------
(* Safety properties *)

\* No two logs diverge: of any two logs, one is a prefix of the other.
NoConflictingLogs ==
    \A i, j \in Server : IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

\* Logs only grow by appending.
AppendOnly ==
    [][\A i \in Server : IsPrefix(cLogs[i], cLogs'[i])]_vars

\* Each step changes exactly one server's log.
SingleServerStep ==
    [][\E i \in Server : Unchanged(i)]_vars

\* Per-action equivalences between existential and axiom-style definitions.
CopySuffixEquiv ==
    [][\A i \in Server :
          (\E j \in Server : CopySuffix(i, j)) <=> CopySuffixAxiom(i)]_vars

ExtendLongestLogEquiv ==
    [][\A i \in Server :
          (\E v \in Value : ExtendLongestLog(i, v)) <=> ExtendLongestLogAxiom(i)]_vars

CopyLongestAndExtendEquiv ==
    [][\A i \in Server :
          (\E j \in Server, v \in Value : CopyLongestAndExtend(i, j, v))
             <=> CopyLongestAndExtendAxiom(i)]_vars

\* Equivalence of the full next-state relations.
NextEquiv == [][Next <=> NextAxiom]_vars

\* State constraint to bound exploration in TLC.
StateConstraint == \A s \in Server : Len(cLogs[s]) <= MaxLogLen

THEOREM Spec => []TypeOK
THEOREM Spec => []NoConflictingLogs
THEOREM Spec => AppendOnly
THEOREM Spec => NextEquiv
=============================================================================