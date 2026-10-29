---------------------------- MODULE MCAbstractRaft ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS s1, s2, s3, MaxLogLen

ASSUME MaxLogLen \in Nat

MCServer == {s1, s2, s3}
Server == MCServer

MCTerms == 2..4
Terms == MCTerms

MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

MCStartTerm == MinOf(MCTerms)
StartTerm == MCStartTerm

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

MCSymmetry == Permutations(MCServer)

Leader == "Leader"
Follower == "Follower"

VARIABLES currentTerm, state, log

vars == <<currentTerm, state, log>>

Quorums == { Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server) }

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))

CanVoteFor(v, i) ==
    \/ LastTerm(log[i]) > LastTerm(log[v])
    \/ /\ LastTerm(log[i]) = LastTerm(log[v])
       /\ Len(log[i]) >= Len(log[v])

TypeOK ==
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Leader, Follower}]
    /\ log \in [Server -> BoundedSeq(Terms, MaxLogLen)]

LogLenConstraint == \A s \in Server : Len(log[s]) <= MaxLogLen

MCStateConstraint ==
    /\ LogLenConstraint
    /\ \A s \in Server : currentTerm[s] \in MCTerms

Init ==
    /\ currentTerm = [s \in Server |-> StartTerm]
    /\ state = [s \in Server |-> Follower]
    /\ log = [s \in Server |-> << >>]

BecomeLeader(i, Q) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in Q
    /\ newTerm \in Terms
    /\ \A v \in Q : currentTerm[v] < newTerm /\ CanVoteFor(v, i)
    /\ currentTerm' = [s \in Server |-> IF s \in Q THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |-> IF s = i THEN Leader
                                  ELSE IF s \in Q THEN Follower
                                  ELSE state[s]]
    /\ UNCHANGED log

ClientRequest(i) ==
    /\ state[i] = Leader
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(@, currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state>>

GetEntries(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ Len(log[j]) > Len(log[i])
    /\ Len(log[i]) < MaxLogLen
    /\ \/ Len(log[i]) = 0
       \/ log[j][Len(log[i])] = log[i][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = Append(@, log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state>>

RollbackEntries(i, j) ==
    /\ i # j
    /\ state[i] = Follower
    /\ Len(log[i]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ ~IsPrefix(log[i], log[j])
    /\ log' = [log EXCEPT ![i] = SubSeq(@, 1, Len(@) - 1)]
    /\ UNCHANGED <<currentTerm, state>>

UpdateTerms(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Follower]
    /\ UNCHANGED log

Next ==
    \/ \E i \in Server, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i, j \in Server : GetEntries(i, j)
    \/ \E i, j \in Server : RollbackEntries(i, j)
    \/ \E i, j \in Server : UpdateTerms(i, j)

Spec == Init /\ [][Next]_vars

OneLeaderPerTerm ==
    \A s, t \in Server :
        (/\ state[s] = Leader
         /\ state[t] = Leader
         /\ currentTerm[s] = currentTerm[t]) => s = t

LogMatching ==
    \A s, t \in Server :
        \A n \in 1..MinOf({Len(log[s]), Len(log[t])}) :
            log[s][n] = log[t][n] => SubSeq(log[s], 1, n) = SubSeq(log[t], 1, n)

TermsBounded == \A s \in Server : currentTerm[s] \in MCTerms

LogTermsBounded ==
    \A s \in Server : \A n \in 1..Len(log[s]) : log[s][n] <= currentTerm[s]

=============================================================================