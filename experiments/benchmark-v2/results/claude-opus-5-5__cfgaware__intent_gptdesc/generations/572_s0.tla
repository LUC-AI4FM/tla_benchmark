---------------------------- MODULE AbsLog ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Servers, Terms, StartTerm

VARIABLE cLogs

ASSUME TermsAssumption ==
    /\ Terms \subseteq Nat
    /\ StartTerm \in Terms
    /\ \A t \in Terms : StartTerm <= t

vars == <<cLogs>>

\* Bound on log length so that the state space stays finite for model checking
MaxLen == Cardinality(Terms) + 1

Last(s) == s[Len(s)]

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

StartLog == <<StartTerm>>

\* A batch of k entries all carrying term t
Batch(k, t) == [x \in 1..k |-> t]

\* True when server i holds a log that every other log is a prefix of
IsMaxLog(i) == \A j \in Servers : IsPrefix(cLogs[j], cLogs[i])

-----------------------------------------------------------------------------
\* Invariants

TypeOK == cLogs \in [Servers -> Seq(Terms)]

NoConflicts ==
    \A i, j \in Servers :
        IsPrefix(cLogs[i], cLogs[j]) \/ IsPrefix(cLogs[j], cLogs[i])

-----------------------------------------------------------------------------
\* Initial state

Init == cLogs = [i \in Servers |-> StartLog]

-----------------------------------------------------------------------------
\* Actions

\* Server i copies a longer prefix of a longer log held by server j
Copy(i) ==
    \E j \in Servers :
        /\ Len(cLogs[j]) > Len(cLogs[i])
        /\ \E l \in (Len(cLogs[i]) + 1)..Len(cLogs[j]) :
              cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, l)]

\* Server i, holding the longest log, appends k entries of some term t
Extend(i, k) ==
    /\ IsMaxLog(i)
    /\ k \in 1..MaxLen
    /\ Len(cLogs[i]) + k <= MaxLen
    /\ \E t \in Terms :
          /\ Last(cLogs[i]) <= t
          /\ cLogs' = [cLogs EXCEPT ![i] = @ \o Batch(k, t)]

\* Axiomatic description of Extend
ExtendAxiom(i) ==
    /\ IsMaxLog(i)
    /\ cLogs' \in [Servers -> Seq(Terms)]
    /\ \A j \in Servers \ {i} : cLogs'[j] = cLogs[j]
    /\ IsPrefix(cLogs[i], cLogs'[i])
    /\ Len(cLogs'[i]) > Len(cLogs[i])
    /\ Len(cLogs'[i]) <= MaxLen
    /\ \E t \in Terms :
          /\ Last(cLogs[i]) <= t
          /\ \A x \in (Len(cLogs[i]) + 1)..Len(cLogs'[i]) : cLogs'[i][x] = t

\* Server i copies the longest log (held by j) and extends it
CopyMaxAndExtend(i) ==
    \E j \in Servers :
        /\ IsMaxLog(j)
        /\ \E k \in 1..MaxLen :
              /\ Len(cLogs[j]) + k <= MaxLen
              /\ \E t \in Terms :
                    /\ Last(cLogs[j]) <= t
                    /\ cLogs' = [cLogs EXCEPT ![i] = cLogs[j] \o Batch(k, t)]

\* Axiomatic description of CopyMaxAndExtend
CopyMaxAndExtendAxiom(i) ==
    /\ cLogs' \in [Servers -> Seq(Terms)]
    /\ \A j \in Servers \ {i} : cLogs'[j] = cLogs[j]
    /\ \E j \in Servers :
          /\ IsMaxLog(j)
          /\ IsPrefix(cLogs[j], cLogs'[i])
          /\ Len(cLogs'[i]) > Len(cLogs[j])
          /\ Len(cLogs'[i]) <= MaxLen
          /\ \E t \in Terms :
                /\ Last(cLogs[j]) <= t
                /\ \A x \in (Len(cLogs[j]) + 1)..Len(cLogs'[i]) :
                      cLogs'[i][x] = t

Next ==
    \E i \in Servers :
        \/ Copy(i)
        \/ \E k \in 1..MaxLen : Extend(i, k)
        \/ CopyMaxAndExtend(i)

AbsSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ \A i \in Servers : WF_vars(Copy(i))

-----------------------------------------------------------------------------
\* Properties

AppendOnlyProp ==
    [][\A i \in Servers : IsPrefix(cLogs[i], cLogs'[i])]_vars

EquivExtendProp ==
    [][\A i \in Servers :
          (\E k \in 1..MaxLen : Extend(i, k)) <=> ExtendAxiom(i)]_vars

EquivCopyMaxAndExtendProp ==
    [][\A i \in Servers :
          CopyMaxAndExtend(i) <=> CopyMaxAndExtendAxiom(i)]_vars

THEOREM AbsSpec => [](TypeOK /\ NoConflicts)
=============================================================================