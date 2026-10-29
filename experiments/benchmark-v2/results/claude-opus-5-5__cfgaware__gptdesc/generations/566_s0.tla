---------------------------- MODULE MCMongoRaftReconfigAbs ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NodeOne, NodeTwo, NodeThree

CONSTANTS Servers, Terms, StartTerm

CONSTANT Seq(_)

VARIABLES currentTerm, state, log, committed

vars == <<currentTerm, state, log, committed>>

-----------------------------------------------------------------------------
(* Sequence helpers. Seq is a constant here, so Sequences is not extended. *)

Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n

Append(s, e) == [i \in 1..(Len(s) + 1) |-> IF i <= Len(s) THEN s[i] ELSE e]

SubSeq(s, m, n) == [i \in 1..(n - m + 1) |-> s[i + m - 1]]

IsPrefix(p, s) == /\ Len(p) <= Len(s)
                  /\ \A i \in 1..Len(p) : p[i] = s[i]

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Quorums == {Q \in SUBSET Servers : Cardinality(Q) * 2 > Cardinality(Servers)}

-----------------------------------------------------------------------------
(* Model-checking configuration *)

MaxLogLen == 3

MCServers == {NodeOne, NodeTwo, NodeThree}

MCTerms == 2..4

MCStartTerm == Min(MCTerms)

MCSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLogLen}

-----------------------------------------------------------------------------
(* Abstract protocol *)

Init ==
    /\ currentTerm = [s \in Servers |-> StartTerm]
    /\ state = [s \in Servers |-> "Follower"]
    /\ log = [s \in Servers |-> <<>>]
    /\ committed = <<>>

BecomeLeader(i, Q) ==
    /\ i \in Q
    /\ currentTerm[i] + 1 \in Terms
    /\ \A q \in Q : currentTerm[q] <= currentTerm[i]
    /\ \A q \in Q : \/ LastTerm(log[i]) > LastTerm(log[q])
                    \/ /\ LastTerm(log[i]) = LastTerm(log[q])
                       /\ Len(log[i]) >= Len(log[q])
    /\ currentTerm' = [s \in Servers |->
                          IF s \in Q THEN currentTerm[i] + 1 ELSE currentTerm[s]]
    /\ state' = [s \in Servers |->
                    IF s = i THEN "Leader"
                    ELSE IF s \in Q THEN "Follower" ELSE state[s]]
    /\ UNCHANGED <<log, committed>>

ClientRequest(i) ==
    /\ state[i] = "Leader"
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

GetEntries(i, j) ==
    /\ state[i] = "Follower"
    /\ Len(log[j]) > Len(log[i])
    /\ \/ Len(log[i]) = 0
       \/ log[i][Len(log[i])] = log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state, committed>>

RollbackEntries(i, j) ==
    /\ state[i] = "Follower"
    /\ Len(log[i]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \/ log[i][Len(log[i])] # log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<currentTerm, state, committed>>

UpdateTerms(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = "Follower"]
    /\ UNCHANGED <<log, committed>>

CommitEntry(i, Q) ==
    LET ind == Len(log[i]) IN
    /\ state[i] = "Leader"
    /\ i \in Q
    /\ ind > Len(committed)
    /\ log[i][ind] = currentTerm[i]
    /\ \A q \in Q : /\ Len(log[q]) >= ind
                    /\ log[q][ind] = log[i][ind]
                    /\ currentTerm[q] = currentTerm[i]
    /\ committed' = SubSeq(log[i], 1, ind)
    /\ UNCHANGED <<currentTerm, state, log>>

Next ==
    \/ \E i \in Servers, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Servers : ClientRequest(i)
    \/ \E i, j \in Servers : GetEntries(i, j)
    \/ \E i, j \in Servers : RollbackEntries(i, j)
    \/ \E i, j \in Servers : UpdateTerms(i, j)
    \/ \E i \in Servers, Q \in Quorums : CommitEntry(i, Q)

AbsSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Type constraints and properties *)

TypeOK ==
    /\ currentTerm \in [Servers -> Terms]
    /\ state \in [Servers -> {"Leader", "Follower"}]
    /\ log \in [Servers -> Seq(Terms)]
    /\ committed \in Seq(Terms)

MCTypeOK ==
    /\ currentTerm \in [MCServers -> MCTerms]
    /\ state \in [MCServers -> {"Leader", "Follower"}]
    /\ log \in [MCServers -> MCSeq(MCTerms)]
    /\ committed \in MCSeq(MCTerms)

NoConflicts ==
    \A s, t \in Servers :
        \A i \in 1..Min({Len(log[s]), Len(log[t])}) :
            log[s][i] = log[t][i] =>
                SubSeq(log[s], 1, i) = SubSeq(log[t], 1, i)

AppendOnlyProp == [][IsPrefix(committed, committed')]_vars

Symmetry ==
    {f \in [MCServers -> MCServers] :
        \A x, y \in MCServers : x # y => f[x] # f[y]}

MaxLogLengthConstraint == \A s \in Servers : Len(log[s]) <= MaxLogLen

=============================================================================