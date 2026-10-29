---------------------------- MODULE AbstractRaft ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Servers, Terms, StartTerm

ASSUME Terms \subseteq Nat
ASSUME StartTerm \in Terms

VARIABLE cLogs

vars == <<cLogs>>

TypeOK == cLogs \in [Servers -> Seq(Terms)]

\* Helper operators
IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

LastTerm(l) == IF Len(l) = 0 THEN StartTerm ELSE l[Len(l)]

IsMaxLog(i) == \A j \in Servers : Len(cLogs[j]) <= Len(cLogs[i])

OthersUnchanged(i) == \A k \in Servers \ {i} : cLogs'[k] = cLogs[k]

\* Server i copies a non-empty suffix of server j's log,
\* where i's log is a strict prefix of j's log.
CopySuffix(i, j) ==
    /\ Len(cLogs[i]) < Len(cLogs[j])
    /\ IsPrefix(cLogs[i], cLogs[j])
    /\ \E k \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
          cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, k)]

\* A server with a longest log extends it by one entry.
ExtendLog(i) ==
    /\ IsMaxLog(i)
    /\ \E t \in Terms :
          /\ t >= LastTerm(cLogs[i])
          /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], t)]

\* Axiom-style formulation of ExtendLog (no existential over new entries).
ExtendLogAxiom(i) ==
    /\ IsMaxLog(i)
    /\ cLogs' \in [Servers -> Seq(Terms)]
    /\ Len(cLogs'[i]) = Len(cLogs[i]) + 1
    /\ SubSeq(cLogs'[i], 1, Len(cLogs[i])) = cLogs[i]
    /\ cLogs'[i][Len(cLogs'[i])] \in Terms
    /\ cLogs'[i][Len(cLogs'[i])] >= LastTerm(cLogs[i])
    /\ OthersUnchanged(i)

\* Server i copies one of the longest logs and extends it by one entry.
CopyMaxAndExtend(i) ==
    \E j \in Servers :
        /\ IsMaxLog(j)
        /\ \E t \in Terms :
              /\ t >= LastTerm(cLogs[j])
              /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[j], t)]

\* Axiom-style formulation of CopyMaxAndExtend.
CopyMaxAndExtendAxiom(i) ==
    \E j \in Servers :
        /\ IsMaxLog(j)
        /\ cLogs' \in [Servers -> Seq(Terms)]
        /\ Len(cLogs'[i]) = Len(cLogs[j]) + 1
        /\ SubSeq(cLogs'[i], 1, Len(cLogs[j])) = cLogs[j]
        /\ cLogs'[i][Len(cLogs'[i])] \in Terms
        /\ cLogs'[i][Len(cLogs'[i])] >= LastTerm(cLogs[j])
        /\ OthersUnchanged(i)

Init == cLogs = [s \in Servers |-> <<>>]

Next ==
    \/ \E i, j \in Servers : CopySuffix(i, j)
    \/ \E i \in Servers : ExtendLog(i)
    \/ \E i \in Servers : CopyMaxAndExtend(i)

AbsSpec == Init /\ [][Next]_vars

\* Properties

\* Logs only ever grow by appending.
AppendOnlyProp ==
    [][\A s \in Servers : IsPrefix(cLogs[s], cLogs'[s])]_vars

\* No two logs ever diverge: one is always a prefix of the other.
NoConflicts ==
    \A i, j \in Servers :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

\* Equivalence between existential action definitions and axiom-style ones.
EquivExtendProp ==
    [][\A s \in Servers : ExtendLog(s) <=> ExtendLogAxiom(s)]_vars

EquivCopyMaxAndExtendProp ==
    [][\A s \in Servers : CopyMaxAndExtend(s) <=> CopyMaxAndExtendAxiom(s)]_vars

=============================================================================