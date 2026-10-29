------------------------------- MODULE CommitLogs -------------------------------
(***************************************************************************)
(* Abstract specification of a distributed consensus algorithm expressed   *)
(* in terms of the commit logs held by a finite set of servers.            *)
(*                                                                         *)
(* Strong observation model: any server can atomically inspect the state   *)
(* of every other server in a single step.                                 *)
(*                                                                         *)
(* Logs are append-only and never diverge. A server may:                   *)
(*   - copy a suffix from another server whose log extends its own,        *)
(*   - extend its log when it is one of the longest logs, or               *)
(*   - copy one of the longest logs and extend it.                         *)
(*                                                                         *)
(* Each action has two forms. The first is an existential definition. The  *)
(* second is an "axiom-style" definition that avoids existential           *)
(* quantification over the next state, which makes refinement checking in  *)
(* TLC cheaper. Temporal properties assert that the two forms are          *)
(* equivalent.                                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Server,   \* finite set of servers
          Value,    \* set of values that may be appended to logs
          MaxLen    \* bound on log length (for finite model checking)

ASSUME /\ IsFiniteSet(Server)
       /\ Server # {}
       /\ MaxLen \in Nat

VARIABLES cLogs

vars == <<cLogs>>

-----------------------------------------------------------------------------
(* Helper operators *)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Range(f) == {f[x] : x \in DOMAIN f}

BoundedSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

IsStrictPrefix(s, t) == IsPrefix(s, t) /\ Len(s) < Len(t)

Compatible(s, t) == IsPrefix(s, t) \/ IsPrefix(t, s)

MaxLogLen == Max({Len(cLogs[s]) : s \in Server})

IsLongest(s) == Len(cLogs[s]) = MaxLogLen

LongestLogs == {cLogs[s] : s \in {t \in Server : IsLongest(t)}}

-----------------------------------------------------------------------------
TypeOK == cLogs \in [Server -> BoundedSeq(Value, MaxLen)]

Init == cLogs = [s \in Server |-> << >>]

-----------------------------------------------------------------------------
(* Existential action definitions *)

(* Server i copies a (non-empty) piece of the suffix of server j's log,   *)
(* where j's log strictly extends i's log.                                 *)
CopySuffix(i) ==
    \E j \in Server :
        /\ IsStrictPrefix(cLogs[i], cLogs[j])
        /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
              cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, k)]

(* Server i holds a longest log and appends a new value to it. *)
ExtendLongest(i) ==
    /\ IsLongest(i)
    /\ Len(cLogs[i]) < MaxLen
    /\ \E v \in Value :
          cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], v)]

(* Server i copies one of the longest logs and extends it with a value. *)
CopyAndExtend(i) ==
    \E j \in Server :
        /\ IsLongest(j)
        /\ Len(cLogs[j]) < MaxLen
        /\ \E v \in Value :
              cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], v)]

Next ==
    \E i \in Server :
        \/ CopySuffix(i)
        \/ ExtendLongest(i)
        \/ CopyAndExtend(i)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Axiom-style action definitions (no existential choice of the new log)  *)

(* Only server i's log changes. *)
OnlyChanges(i) == \A s \in Server \ {i} : cLogs'[s] = cLogs[s]

CopySuffixAxiom(i) ==
    /\ cLogs' \in [Server -> Seq(Value)]
    /\ OnlyChanges(i)
    /\ IsStrictPrefix(cLogs[i], cLogs'[i])
    /\ \E j \in Server : IsPrefix(cLogs'[i], cLogs[j])

ExtendLongestAxiom(i) ==
    /\ cLogs' \in [Server -> Seq(Value)]
    /\ OnlyChanges(i)
    /\ IsLongest(i)
    /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
    /\ Len(cLogs'[i]) <= MaxLen
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ cLogs'[i][Len(cLogs'[i])] \in Value

CopyAndExtendAxiom(i) ==
    /\ cLogs' \in [Server -> Seq(Value)]
    /\ OnlyChanges(i)
    /\ Len(cLogs'[i]) = MaxLogLen + 1
    /\ Len(cLogs'[i]) <= MaxLen
    /\ SubSeq(cLogs'[i], 1, MaxLogLen) \in LongestLogs
    /\ cLogs'[i][Len(cLogs'[i])] \in Value

NextAxiom ==
    \E i \in Server :
        \/ CopySuffixAxiom(i)
        \/ ExtendLongestAxiom(i)
        \/ CopyAndExtendAxiom(i)

SpecAxiom == Init /\ [][NextAxiom]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

(* No two logs conflict: every pair of logs is prefix-related. *)
NoConflicts == \A i, j \in Server : Compatible(cLogs[i], cLogs[j])

(* Logs only ever grow by appending. *)
AppendOnly ==
    [][\A s \in Server : IsPrefix(cLogs[s], cLogs'[s])]_vars

(* Logs never diverge across any step. *)
NeverDiverge == []NoConflicts

(* Equivalence between existential and axiom-style formulations. *)
CopySuffixEquiv ==
    [][\A i \in Server : CopySuffix(i) <=> CopySuffixAxiom(i)]_vars

ExtendLongestEquiv ==
    [][\A i \in Server : ExtendLongest(i) <=> ExtendLongestAxiom(i)]_vars

CopyAndExtendEquiv ==
    [][\A i \in Server : CopyAndExtend(i) <=> CopyAndExtendAxiom(i)]_vars

NextEquiv == [][Next <=> NextAxiom]_vars

(* State constraint for bounded model checking. *)
StateConstraint == \A s \in Server : Len(cLogs[s]) <= MaxLen

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []NoConflicts
THEOREM Spec => AppendOnly
THEOREM Spec => NextEquiv
=============================================================================