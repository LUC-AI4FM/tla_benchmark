---------------------------- MODULE abs ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Server,       \* set of server nodes (e.g. {s1, s2, s3})
          Terms,        \* range of terms (e.g. 2..4)
          StartTerm,    \* starting term
          MaxLogLen,    \* bound on log length (e.g. 7)
          MaxExtend     \* max number of entries appended at once (e.g. 3)

ASSUME /\ Terms \subseteq Nat
       /\ StartTerm \in Nat
       /\ MaxLogLen \in Nat
       /\ MaxExtend \in Nat \ {0}

VARIABLES cLogs

vars == <<cLogs>>

-----------------------------------------------------------------------------
(* Helpers *)

Min(a, b) == IF a < b THEN a ELSE b

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ s = SubSeq(t, 1, Len(s))

LastTerm(log) == IF Len(log) = 0 THEN StartTerm ELSE log[Len(log)]

-----------------------------------------------------------------------------
(* Initial state: all logs are empty *)

Init == cLogs = [s \in Server |-> << >>]

(* A server whose log extends every other log appends between 1 and
   MaxExtend entries of a term no smaller than its last term. *)
ExtendLog(s, k, term) ==
    /\ Len(cLogs[s]) + k <= MaxLogLen
    /\ \A t \in Server : IsPrefix(cLogs[t], cLogs[s])
    /\ term >= LastTerm(cLogs[s])
    /\ term >= StartTerm
    /\ cLogs' = [cLogs EXCEPT ![s] = @ \o [i \in 1..k |-> term]]

(* A server copies a longer prefix of another server's log
   (replication), only ever growing its own log. *)
CopyLog(s, t, n) ==
    /\ s # t
    /\ IsPrefix(cLogs[s], cLogs[t])
    /\ Len(cLogs[s]) < n
    /\ n <= Len(cLogs[t])
    /\ n - Len(cLogs[s]) <= MaxExtend
    /\ cLogs' = [cLogs EXCEPT ![s] = SubSeq(cLogs[t], 1, n)]

Next ==
    \/ \E s \in Server, k \in 1..MaxExtend, term \in Terms : ExtendLog(s, k, term)
    \/ \E s, t \in Server, n \in 1..MaxLogLen : CopyLog(s, t, n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Model-checking configuration helpers *)

StateConstraint == \A s \in Server : Len(cLogs[s]) <= MaxLogLen

Symmetry == Permutations(Server)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == cLogs \in [Server -> BoundedSeq(Terms, MaxLogLen)]

NoConflicts ==
    \A s, t \in Server :
        \A i \in 1..Min(Len(cLogs[s]), Len(cLogs[t])) :
            cLogs[s][i] = cLogs[t][i]

(* Temporal property: logs are append-only *)
AppendOnlyProp ==
    [][\A s \in Server : IsPrefix(cLogs[s], cLogs'[s])]_vars

THEOREM Spec => [](TypeOK /\ NoConflicts) /\ AppendOnlyProp
=============================================================================