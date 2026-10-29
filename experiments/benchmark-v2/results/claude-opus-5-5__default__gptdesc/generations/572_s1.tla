------------------------------- MODULE AbstractCommitLogs -------------------------------
(***************************************************************************)
(* Abstract specification of a distributed consensus algorithm in terms   *)
(* of commit logs kept by a finite set of servers. It uses a strong       *)
(* observation model: any node can atomically inspect the state of all    *)
(* other nodes.                                                           *)
(*                                                                         *)
(* Logs are append-only and never diverge. A server can:                  *)
(*   - copy a suffix from another server's log,                           *)
(*   - extend a longest log, or                                           *)
(*   - copy one of the longest logs and extend it.                        *)
(*                                                                         *)
(* Each action has an existential definition and an equivalent            *)
(* axiom-style definition. The axiom-style forms are cheaper for TLC to   *)
(* evaluate during refinement checking.                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Server,      \* The finite set of servers.
    Value,       \* The set of values that may appear in log entries.
    MaxLogLen    \* Bound on log length, used only for model checking.

ASSUME /\ IsFiniteSet(Server)
       /\ Server # {}
       /\ MaxLogLen \in Nat

VARIABLE cLogs   \* cLogs[s] is the commit log of server s.

vars == <<cLogs>>

---------------------------------------------------------------------------
(* Helper operators *)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

IsStrictPrefix(s, t) == IsPrefix(s, t) /\ Len(s) < Len(t)

Last(s) == s[Len(s)]

IsLongest(i) == \A j \in Server : Len(cLogs[i]) >= Len(cLogs[j])

\* All other servers keep their logs unchanged.
OthersUnchanged(i) == \A j \in Server \ {i} : cLogs'[j] = cLogs[j]

TypeOK == cLogs \in [Server -> Seq(Value)]

---------------------------------------------------------------------------
(* Initial state: every log is empty *)

Init == cLogs = [s \in Server |-> << >>]

---------------------------------------------------------------------------
(* Existential action definitions *)

\* Server i copies a non-empty suffix of server j's log. Its log must
\* already be a strict prefix of j's log.
CopySuffix(i, j) ==
    /\ IsStrictPrefix(cLogs[i], cLogs[j])
    /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
          cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, k)]

\* Server i holds a longest log and appends a new value to it.
ExtendLongest(i, v) ==
    /\ IsLongest(i)
    /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], v)]

\* Server i copies a longest log (held by j) and appends a new value.
CopyAndExtend(i, j, v) ==
    /\ IsLongest(j)
    /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], v)]

CopySuffixExists    == \E i, j \in Server : CopySuffix(i, j)
ExtendLongestExists == \E i \in Server, v \in Value : ExtendLongest(i, v)
CopyAndExtendExists == \E i, j \in Server, v \in Value : CopyAndExtend(i, j, v)

Next ==
    \/ CopySuffixExists
    \/ ExtendLongestExists
    \/ CopyAndExtendExists

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Axiom-style formulations (for efficient refinement checking in TLC) *)

CopySuffixAxiom ==
    \E i, j \in Server :
        /\ DOMAIN cLogs' = Server
        /\ OthersUnchanged(i)
        /\ Len(cLogs'[i]) > Len(cLogs[i])
        /\ IsPrefix(cLogs[i], cLogs'[i])
        /\ IsPrefix(cLogs'[i], cLogs[j])

ExtendLongestAxiom ==
    \E i \in Server :
        /\ DOMAIN cLogs' = Server
        /\ IsLongest(i)
        /\ OthersUnchanged(i)
        /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
        /\ IsPrefix(cLogs[i], cLogs'[i])
        /\ Last(cLogs'[i]) \in Value

CopyAndExtendAxiom ==
    \E i, j \in Server :
        /\ DOMAIN cLogs' = Server
        /\ IsLongest(j)
        /\ OthersUnchanged(i)
        /\ Len(cLogs'[i]) = Len(cLogs[j]) + 1
        /\ IsPrefix(cLogs[j], cLogs'[i])
        /\ Last(cLogs'[i]) \in Value

NextAxiom ==
    \/ CopySuffixAxiom
    \/ ExtendLongestAxiom
    \/ CopyAndExtendAxiom

SpecAxiom == Init /\ [][NextAxiom]_vars

---------------------------------------------------------------------------
(* Safety properties *)

\* Logs only ever grow by appending.
AppendOnly ==
    [][\A s \in Server : IsPrefix(cLogs[s], cLogs'[s])]_vars

\* No two logs conflict: one is always a prefix of the other.
NoConflict ==
    \A i, j \in Server :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

NoConflictProp == []NoConflict

\* Equivalence of the existential and axiom-style action definitions.
CopySuffixEquiv    == [][CopySuffixExists    <=> CopySuffixAxiom]_vars
ExtendLongestEquiv == [][ExtendLongestExists <=> ExtendLongestAxiom]_vars
CopyAndExtendEquiv == [][CopyAndExtendExists <=> CopyAndExtendAxiom]_vars
NextEquiv          == [][Next <=> NextAxiom]_vars

---------------------------------------------------------------------------
(* Model checking support *)

StateConstraint == \A s \in Server : Len(cLogs[s]) <= MaxLogLen

---------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => NoConflictProp
THEOREM Spec => AppendOnly
THEOREM Spec => NextEquiv
=============================================================================