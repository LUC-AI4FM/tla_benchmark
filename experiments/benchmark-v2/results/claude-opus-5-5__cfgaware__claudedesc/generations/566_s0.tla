---------------------------- MODULE MCabs ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NodeOne, NodeTwo, NodeThree

CONSTANTS Servers, Terms, StartTerm

VARIABLE cLogs

-----------------------------------------------------------------------------
(* Sequence helpers (Sequences is not extended so that Seq can be overridden) *)

Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n

SubSeq(s, m, n) == [k \in 1..(1 + n - m) |-> s[k + m - 1]]

Append(s, e) == [k \in 1..(Len(s) + 1) |-> IF k <= Len(s) THEN s[k] ELSE e]

Seq(S) == UNION {[1..n -> S] : n \in Nat}

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A k \in 1..Len(s) : s[k] = t[k]

-----------------------------------------------------------------------------
(* Model-checking parameters *)

MaxLogLength == 7
MaxExtension == 3

MCServers == {NodeOne, NodeTwo, NodeThree}
MCTerms == 2..4
MCStartTerm == 1

MCSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLogLength}

-----------------------------------------------------------------------------
(* Abstract log specification *)

AllTerms == {cLogs[s][k] : s \in Servers, k \in DOMAIN cLogs[s]}

MaxTerm ==
    IF AllTerms = {} THEN StartTerm
    ELSE CHOOSE t \in AllTerms : \A u \in AllTerms : u <= t

LastTerm(log) == IF Len(log) = 0 THEN StartTerm ELSE log[Len(log)]

Init == cLogs = [s \in Servers |-> << >>]

\* A leader appends a fresh entry of the newest term (or continues the newest term).
NewEntry(i, t) ==
    /\ t \in Terms
    /\ \/ t > MaxTerm
       \/ /\ t = MaxTerm
          /\ Len(cLogs[i]) > 0
          /\ LastTerm(cLogs[i]) = t
    /\ cLogs' = [cLogs EXCEPT ![i] = Append(cLogs[i], t)]

\* A server extends its log by copying up to MaxExtension entries from another log.
ExtendLog(i, j) ==
    /\ i # j
    /\ IsPrefix(cLogs[i], cLogs[j])
    /\ Len(cLogs[j]) > Len(cLogs[i])
    /\ \E n \in 1..MaxExtension :
         /\ Len(cLogs[i]) + n <= Len(cLogs[j])
         /\ cLogs' = [cLogs EXCEPT ![i] = SubSeq(cLogs[j], 1, Len(cLogs[i]) + n)]

Next ==
    \/ \E i \in Servers, t \in Terms : NewEntry(i, t)
    \/ \E i, j \in Servers : ExtendLog(i, j)

AbsSpec == Init /\ [][Next]_cLogs

-----------------------------------------------------------------------------
(* Properties *)

TypeOK == cLogs \in [Servers -> Seq(Terms)]

MCTypeOK == cLogs \in [Servers -> MCSeq(Terms)]

NoConflicts ==
    \A i, j \in Servers :
        \A k \in (DOMAIN cLogs[i]) \cap (DOMAIN cLogs[j]) :
            cLogs[i][k] = cLogs[j][k] =>
                \A m \in 1..k : cLogs[i][m] = cLogs[j][m]

AppendOnlyProp ==
    [][\A s \in Servers : IsPrefix(cLogs[s], cLogs'[s])]_cLogs

Symmetry ==
    {f \in [MCServers -> MCServers] :
        \A x \in MCServers : \E y \in MCServers : f[y] = x}

MaxLogLengthConstraint ==
    \A s \in Servers : Len(cLogs[s]) <= MaxLogLength

=============================================================================