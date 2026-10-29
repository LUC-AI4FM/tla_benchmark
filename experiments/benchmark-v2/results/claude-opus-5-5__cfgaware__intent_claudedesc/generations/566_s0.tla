------------------------------ MODULE AbstractReplicatedLog ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    NodeOne, NodeTwo, NodeThree,
    Servers,
    Terms,
    StartTerm

VARIABLES logs

vars == <<logs>>

----------------------------------------------------------------------------------------
\* Sequence helpers (defined locally so that Seq can be overridden by MCSeq)

Seq(S) == UNION { [1..n -> S] : n \in Nat }

Len(s) == Cardinality(DOMAIN s)

Append(s, e) == [i \in 1..(Len(s) + 1) |-> IF i <= Len(s) THEN s[i] ELSE e]

IsPrefix(a, b) ==
    /\ Len(a) <= Len(b)
    /\ \A i \in 1..Len(a) : a[i] = b[i]

LastTerm(l) == IF Len(l) = 0 THEN StartTerm ELSE l[Len(l)]

----------------------------------------------------------------------------------------
\* Model checking definitions

MaxLogLength == 3

MCServers == {NodeOne, NodeTwo, NodeThree}

MCTerms == 1..2

MCStartTerm == 1

MCSeq(S) == UNION { [1..n -> S] : n \in 0..MaxLogLength }

Symmetry ==
    { f \in [MCServers -> MCServers] :
        \A x, y \in MCServers : f[x] = f[y] => x = y }

----------------------------------------------------------------------------------------
\* Abstract model

Init == logs = [s \in Servers |-> << >>]

\* A server whose log extends every other log may append a new entry
\* whose term is not smaller than its last term.
AppendEntry(s, t) ==
    /\ \A r \in Servers : IsPrefix(logs[r], logs[s])
    /\ t \in Terms
    /\ t >= StartTerm
    /\ t >= LastTerm(logs[s])
    /\ logs' = [logs EXCEPT ![s] = Append(logs[s], t)]

\* Abstract convergence: a lagging server copies the next entry from a
\* server with a longer log.
CopyEntry(s, r) ==
    /\ s # r
    /\ Len(logs[s]) < Len(logs[r])
    /\ IsPrefix(logs[s], logs[r])
    /\ logs' = [logs EXCEPT ![s] = Append(logs[s], logs[r][Len(logs[s]) + 1])]

Next ==
    \/ \E s \in Servers, t \in Terms : AppendEntry(s, t)
    \/ \E s, r \in Servers : CopyEntry(s, r)

AbsSpec == Init /\ [][Next]_vars

----------------------------------------------------------------------------------------
\* Properties

TypeOK == logs \in [Servers -> Seq(Terms)]

MCTypeOK == \A s \in Servers : logs[s] \in MCSeq(Terms)

NoConflicts ==
    \A s, r \in Servers : IsPrefix(logs[s], logs[r]) \/ IsPrefix(logs[r], logs[s])

AppendOnlyProp ==
    [][\A s \in Servers : IsPrefix(logs[s], logs'[s])]_vars

MaxLogLengthConstraint ==
    \A s \in Servers : Len(logs[s]) <= MaxLogLength

=========================================================================================