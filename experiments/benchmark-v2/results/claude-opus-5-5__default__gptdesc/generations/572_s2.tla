------------------------------- MODULE CommitLogs -------------------------------
(***************************************************************************)
(* Abstract specification of a distributed consensus algorithm in terms   *)
(* of the commit logs kept by a finite set of servers.                     *)
(*                                                                         *)
(* It assumes a strong observation model: any node can atomically inspect *)
(* the state of every other node. Logs are append-only and never diverge.  *)
(* A server may                                                            *)
(*   - copy a suffix from another server's log,                            *)
(*   - extend a longest log, or                                            *)
(*   - copy one of the longest logs and extend it.                         *)
(*                                                                         *)
(* Each action has two forms: an existential (constructive) definition and *)
(* an axiom-style definition. The axiom style constrains cLogs' directly,  *)
(* which makes refinement checking in TLC more efficient. Temporal         *)
(* properties assert that the two forms are equivalent.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server,     \* finite set of servers
          Value,      \* finite set of values that may be committed
          MaxLogLen   \* bound on log length (used only for TLC state constraint)

ASSUME /\ IsFiniteSet(Server)
       /\ Server # {}
       /\ IsFiniteSet(Value)
       /\ Value # {}
       /\ MaxLogLen \in Nat

VARIABLE cLogs

vars == << cLogs >>

-----------------------------------------------------------------------------
(* Helper operators *)

\* s is a prefix of t
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

\* s is a strict prefix of t
IsStrictPrefix(s, t) ==
    /\ IsPrefix(s, t)
    /\ Len(s) < Len(t)

\* The log of server i is a longest log
IsLongest(i) == \A j \in Server : Len(cLogs[i]) >= Len(cLogs[j])

\* Every server other than i keeps its log
OthersUnchanged(i) == \A k \in Server \ {i} : cLogs'[k] = cLogs[k]

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ DOMAIN cLogs = Server
    /\ \A i \in Server : cLogs[i] \in Seq(Value)

-----------------------------------------------------------------------------
(* Initial state *)

Init == cLogs = [i \in Server |-> << >>]

-----------------------------------------------------------------------------
(* Existential (constructive) action definitions *)

\* Server i copies part of a suffix of j's log, where i's log is a strict
\* prefix of j's log.
CopySuffix(i, j) ==
    /\ IsStrictPrefix(cLogs[i], cLogs[j])
    /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
          cLogs' = [cLogs EXCEPT ![i] = cLogs[i] \o
                                        SubSeq(cLogs[j], Len(cLogs[i]) + 1, k)]

\* Server i holds a longest log and extends it with a new value.
ExtendLongestLog(i) ==
    /\ IsLongest(i)
    /\ \E v \in Value :
          cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], v)]

\* Server i copies a longest log (held by j) and extends it with a new value.
CopyAndExtendLongestLog(i, j) ==
    /\ IsLongest(j)
    /\ \E v \in Value :
          cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], v)]

Next ==
    \/ \E i, j \in Server : CopySuffix(i, j)
    \/ \E i \in Server : ExtendLongestLog(i)
    \/ \E i, j \in Server : CopyAndExtendLongestLog(i, j)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Axiom-style action definitions (no existential over the new state)     *)

CopySuffixAxiom(i, j) ==
    /\ IsStrictPrefix(cLogs[i], cLogs[j])
    /\ DOMAIN cLogs' = Server
    /\ IsPrefix(cLogs'[i], cLogs[j])
    /\ Len(cLogs'[i]) > Len(cLogs[i])
    /\ OthersUnchanged(i)

ExtendLongestLogAxiom(i) ==
    /\ IsLongest(i)
    /\ DOMAIN cLogs' = Server
    /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ cLogs'[i][Len(cLogs'[i])] \in Value
    /\ OthersUnchanged(i)

CopyAndExtendLongestLogAxiom(i, j) ==
    /\ IsLongest(j)
    /\ DOMAIN cLogs' = Server
    /\ Len(cLogs'[i]) = Len(cLogs[j]) + 1
    /\ IsPrefix(cLogs[j], cLogs'[i])
    /\ cLogs'[i][Len(cLogs'[i])] \in Value
    /\ OthersUnchanged(i)

NextAxiom ==
    \/ \E i, j \in Server : CopySuffixAxiom(i, j)
    \/ \E i \in Server : ExtendLongestLogAxiom(i)
    \/ \E i, j \in Server : CopyAndExtendLongestLogAxiom(i, j)

SpecAxiom == Init /\ [][NextAxiom]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

\* Logs never diverge: any two logs are related by the prefix order.
NoConflictingLogs ==
    \A i, j \in Server :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

\* Logs only grow: each step extends logs and never rewrites them.
AppendOnly ==
    [][\A i \in Server : IsPrefix(cLogs[i], cLogs'[i])]_vars

\* Equivalence between existential and axiom-style action definitions.
CopySuffixEquiv ==
    [][\A i, j \in Server : CopySuffix(i, j) <=> CopySuffixAxiom(i, j)]_vars

ExtendLongestLogEquiv ==
    [][\A i \in Server : ExtendLongestLog(i) <=> ExtendLongestLogAxiom(i)]_vars

CopyAndExtendLongestLogEquiv ==
    [][\A i, j \in Server :
          CopyAndExtendLongestLog(i, j) <=> CopyAndExtendLongestLogAxiom(i, j)]_vars

NextEquiv == [][Next <=> NextAxiom]_vars

-----------------------------------------------------------------------------
(* State constraint for bounding TLC exploration *)

StateConstraint == \A i \in Server : Len(cLogs[i]) <= MaxLogLen

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []NoConflictingLogs
THEOREM Spec => AppendOnly
THEOREM Spec => NextEquiv
=============================================================================