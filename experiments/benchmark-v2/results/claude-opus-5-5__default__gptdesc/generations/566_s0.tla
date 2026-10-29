---------------------------- MODULE MCAbstractRaft ----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\* Concrete server identities (instantiate as model values in the TLC config)
CONSTANTS n1, n2, n3

\* Upper bound on log length, used for finite exploration
CONSTANT MaxLogLen

ASSUME MaxLogLen \in Nat

-----------------------------------------------------------------------------
\* Model-checking configuration helpers

\* The concrete symmetric server set of three nodes
MCServer == {n1, n2, n3}

\* The bounded range of terms
MCTerms == 2..4

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* The start term is the minimum of the term range
MCInitTerm == Min(MCTerms)
MCMaxTerm  == Max(MCTerms)

\* Sequences over S with length at most n
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

MCLogType == BoundedSeq(MCTerms, MaxLogLen)

\* Symmetry reduction through permutations of the server set
MCSymmetry == Permutations(MCServer)

-----------------------------------------------------------------------------
\* Abstraction (inlined so the module is self-contained)

Server == MCServer
Terms  == MCTerms

Secondary == "Secondary"
Primary   == "Primary"

VARIABLES currentTerm, state, log, committed

vars == <<currentTerm, state, log, committed>>

Quorums == { Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server) }

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* j's log is at least as up to date as i's log
LogOk(i, j) ==
    \/ LastTerm(log[j]) > LastTerm(log[i])
    \/ /\ LastTerm(log[j]) = LastTerm(log[i])
       /\ Len(log[j]) >= Len(log[i])

CanVoteForOplog(i, j, term) ==
    /\ currentTerm[i] < term
    /\ LogOk(i, j)

CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ Len(log[j]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \/ log[i][Len(log[i])] # log[j][Len(log[i])]

-----------------------------------------------------------------------------
\* Type constraints

TypeOK ==
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Secondary, Primary}]
    /\ log \in [Server -> MCLogType]
    /\ committed \subseteq ((1..MaxLogLen) \X Terms)

\* Explicit log length constraint
MCLogLenConstraint == \A s \in Server : Len(log[s]) <= MaxLogLen

\* State constraint for the model checker
MCStateConstraint ==
    /\ MCLogLenConstraint
    /\ \A s \in Server : currentTerm[s] \in MCTerms

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ currentTerm = [s \in Server |-> MCInitTerm]
    /\ state = [s \in Server |-> Secondary]
    /\ log = [s \in Server |-> <<>>]
    /\ committed = {}

-----------------------------------------------------------------------------
\* Actions

ClientRequest(i) ==
    /\ state[i] = Primary
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

GetEntries(i, j) ==
    /\ state[i] = Secondary
    /\ Len(log[j]) > Len(log[i])
    /\ Len(log[i]) < MaxLogLen
    /\ \/ Len(log[i]) = 0
       \/ log[j][Len(log[i])] = log[i][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state, committed>>

RollbackEntries(i, j) ==
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<currentTerm, state, committed>>

BecomeLeader(i, voteQuorum) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ newTerm \in MCTerms
    /\ i \in voteQuorum
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    /\ currentTerm' = [s \in Server |->
                          IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary
                    ELSE state[s]]
    /\ UNCHANGED <<log, committed>>

CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    /\ state[i] = Primary
    /\ ind > 0
    /\ i \in commitQuorum
    /\ log[i][ind] = currentTerm[i]
    /\ \A s \in commitQuorum :
          /\ Len(log[s]) >= ind
          /\ log[s][ind] = log[i][ind]
          /\ currentTerm[s] = currentTerm[i]
    /\ committed' = committed \cup { <<ind, currentTerm[i]>> }
    /\ UNCHANGED <<currentTerm, state, log>>

UpdateTerms(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]
    /\ UNCHANGED <<log, committed>>

-----------------------------------------------------------------------------
\* Next-state relation and specification

Next ==
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums : BecomeLeader(s, Q)
    \/ \E s \in Server : \E Q \in Quorums : CommitEntry(s, Q)
    \/ \E s, t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants

\* At most one primary per term
ElectionSafety ==
    \A s, t \in Server :
        (state[s] = Primary /\ state[t] = Primary /\ currentTerm[s] = currentTerm[t])
            => s = t

\* No two different entries are committed at the same index
StateMachineSafety ==
    \A c1, c2 \in committed : c1[1] = c2[1] => c1 = c2

\* A primary of a later term contains all previously committed entries
LeaderCompleteness ==
    \A s \in Server :
        state[s] = Primary =>
            \A c \in committed :
                c[2] < currentTerm[s] =>
                    /\ Len(log[s]) >= c[1]
                    /\ log[s][c[1]] = c[2]

THEOREM Spec => [](TypeOK /\ ElectionSafety /\ StateMachineSafety)
=============================================================================