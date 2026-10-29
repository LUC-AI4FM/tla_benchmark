------------------------------- MODULE AbstractCommitLog -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server,       \* finite set of servers
          Value,        \* set of values that may be appended to logs
          MaxLogLen     \* bound on log length (for finite model checking with TLC)

ASSUME /\ IsFiniteSet(Server)
       /\ Server # {}
       /\ MaxLogLen \in Nat

VARIABLE cLogs          \* cLogs[s] is the commit log of server s

vars == <<cLogs>>

-----------------------------------------------------------------------------------------
(* Helper operators *)

Range(f) == {f[x] : x \in DOMAIN f}

\* s is a prefix of t
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

\* Logs that are bounded by MaxLogLen
BoundedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLogLen}

\* Server i holds one of the longest logs
IsLongest(i) == \A k \in Server : Len(cLogs[k]) <= Len(cLogs[i])

\* Every server other than i keeps its log
OthersUnchanged(i) ==
    /\ DOMAIN cLogs' = Server
    /\ \A k \in Server \ {i} : cLogs'[k] = cLogs[k]

-----------------------------------------------------------------------------------------
(* Type invariant *)

TypeOK == cLogs \in [Server -> BoundedSeq(Value)]

-----------------------------------------------------------------------------------------
(* Initial state *)

Init == cLogs = [s \in Server |-> <<>>]

-----------------------------------------------------------------------------------------
(* Actions (existential definitions). Strong observation model: a server can
   atomically inspect the logs of all other servers. *)

\* Server i copies a (nonempty) suffix of server j's log, where i's log is a prefix of j's.
CopySuffix(i, j) ==
    /\ IsPrefix(cLogs[i], cLogs[j])
    /\ Len(cLogs[i]) < Len(cLogs[j])
    /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
          cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, k)]

\* Server i, holding a longest log, extends its own log by one value.
ExtendLog(i) ==
    /\ IsLongest(i)
    /\ Len(cLogs[i]) < MaxLogLen
    /\ \E v \in Value :
          cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], v)]

\* Server i copies a longest log (held by j) and extends it by one value.
CopyAndExtend(i, j) ==
    /\ IsLongest(j)
    /\ Len(cLogs[j]) < MaxLogLen
    /\ \E v \in Value :
          cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], v)]

-----------------------------------------------------------------------------------------
(* Axiom-style formulations of the same actions (efficient for refinement checking) *)

CopySuffixAxiom(i, j) ==
    /\ OthersUnchanged(i)
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ IsPrefix(cLogs'[i], cLogs[j])
    /\ Len(cLogs'[i]) > Len(cLogs[i])

ExtendLogAxiom(i) ==
    /\ IsLongest(i)
    /\ Len(cLogs[i]) < MaxLogLen
    /\ OthersUnchanged(i)
    /\ cLogs'[i] \in Seq(Value)
    /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
    /\ IsPrefix(cLogs[i], cLogs'[i])

CopyAndExtendAxiom(i, j) ==
    /\ IsLongest(j)
    /\ Len(cLogs[j]) < MaxLogLen
    /\ OthersUnchanged(i)
    /\ cLogs'[i] \in Seq(Value)
    /\ Len(cLogs'[i]) = Len(cLogs[j]) + 1
    /\ IsPrefix(cLogs[j], cLogs'[i])

-----------------------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ \E i, j \in Server : CopySuffix(i, j)
    \/ \E i \in Server : ExtendLog(i)
    \/ \E i, j \in Server : CopyAndExtend(i, j)

NextAxiom ==
    \/ \E i, j \in Server : CopySuffixAxiom(i, j)
    \/ \E i \in Server : ExtendLogAxiom(i)
    \/ \E i, j \in Server : CopyAndExtendAxiom(i, j)

Spec == Init /\ [][Next]_vars

SpecAxiom == Init /\ [][NextAxiom]_vars

-----------------------------------------------------------------------------------------
(* Safety properties *)

\* Logs never diverge: any two logs are related by the prefix order.
NoConflictingLogs ==
    \A i, j \in Server :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

\* Logs only grow by appending.
AppendOnlyStep == \A s \in Server : IsPrefix(cLogs[s], cLogs'[s])

AppendOnly == [][AppendOnlyStep]_vars

\* Equivalence between existential and axiom-style action definitions.
CopySuffixEquiv ==
    [][\A i, j \in Server : CopySuffix(i, j) <=> CopySuffixAxiom(i, j)]_vars

ExtendLogEquiv ==
    [][\A i \in Server : ExtendLog(i) <=> ExtendLogAxiom(i)]_vars

CopyAndExtendEquiv ==
    [][\A i, j \in Server : CopyAndExtend(i, j) <=> CopyAndExtendAxiom(i, j)]_vars

NextEquiv == [][Next <=> NextAxiom]_vars

\* The axiom-style spec refines the existential spec and vice versa.
AxiomRefinesSpec == SpecAxiom => Spec
SpecRefinesAxiom == Spec => SpecAxiom

THEOREM Spec => []TypeOK
THEOREM Spec => []NoConflictingLogs
THEOREM Spec => AppendOnly
THEOREM Spec => CopySuffixEquiv /\ ExtendLogEquiv /\ CopyAndExtendEquiv /\ NextEquiv
=========================================================================================