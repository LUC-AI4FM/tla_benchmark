---------------------------- MODULE MCAbstractRaft ----------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

CONSTANTS n1, n2, n3      \* concrete model values for the three servers
CONSTANTS MaxLogLen       \* bound on log length
CONSTANTS Follower, Leader

VARIABLES currentTerm, state, log, committed

vars == <<currentTerm, state, log, committed>>

(***************************************************************************)
(* Model-checking configuration helpers                                    *)
(***************************************************************************)

MCServer == {n1, n2, n3}
Server == MCServer

MCTerms == 2..4
Terms == MCTerms

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

MCStartTerm == Min(MCTerms)
StartTerm == MCStartTerm

\* All sequences over S with length at most n.
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

MCLogTerms == MCTerms
MCLogs == BoundedSeq(MCLogTerms, MaxLogLen)

\* Symmetry reduction through permutations of the server set.
ServerSymmetry == Permutations(MCServer)

(***************************************************************************)
(* Underlying abstraction (inlined so the module is self-contained)        *)
(***************************************************************************)

Quorums == { Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server) }

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ Len(log[i]) >= Len(log[j])

InLog(e, i) == /\ Len(log[i]) >= e[1]
               /\ log[i][e[1]] = e[2]

\* Leader election in a single step using a quorum of voters.
BecomeLeader(i, Q) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in Q
    /\ newTerm \in Terms
    /\ \A v \in Q : currentTerm[v] < newTerm
    /\ \A v \in Q : IsUpToDate(i, v)
    /\ currentTerm' = [s \in Server |-> IF s \in Q THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |-> IF s = i THEN Leader
                                  ELSE IF s \in Q THEN Follower ELSE state[s]]
    /\ UNCHANGED <<log, committed>>

\* A leader appends a new entry from its current term.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Server i pulls the next entry from server j's log.
GetEntries(i, j) ==
    /\ state[i] = Follower
    /\ Len(log[j]) > Len(log[i])
    /\ Len(log[i]) < MaxLogLen
    /\ \/ Len(log[i]) = 0
       \/ log[i][Len(log[i])] = log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Server i rolls back a divergent entry relative to a more up-to-date j.
RollbackEntries(i, j) ==
    /\ Len(log[i]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \/ log[i][Len(log[i])] # log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* A leader commits its latest entry once a quorum has it in the current term.
CommitEntry(i, Q) ==
    LET ind == Len(log[i]) IN
    /\ state[i] = Leader
    /\ ind > 0
    /\ log[i][ind] = currentTerm[i]
    /\ \A s \in Q : /\ Len(log[s]) >= ind
                    /\ log[s][ind] = log[i][ind]
                    /\ currentTerm[s] = currentTerm[i]
    /\ committed' = committed \cup
                    {[entry |-> <<ind, currentTerm[i]>>, term |-> currentTerm[i]]}
    /\ UNCHANGED <<currentTerm, state, log>>

\* Term propagation between servers.
UpdateTerms(i, j) ==
    /\ currentTerm[i] < currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<log, committed>>

Init ==
    /\ currentTerm = [s \in Server |-> StartTerm]
    /\ state = [s \in Server |-> Follower]
    /\ log = [s \in Server |-> <<>>]
    /\ committed = {}

Next ==
    \/ \E i \in Server, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i, j \in Server : GetEntries(i, j)
    \/ \E i, j \in Server : RollbackEntries(i, j)
    \/ \E i \in Server, Q \in Quorums : CommitEntry(i, Q)
    \/ \E i, j \in Server : UpdateTerms(i, j)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type constraints and state constraints                                  *)
(***************************************************************************)

TypeOK ==
    /\ currentTerm \in [Server -> Terms]
    /\ state \in [Server -> {Follower, Leader}]
    /\ log \in [Server -> Seq(Terms)]
    /\ committed \subseteq [entry : Nat \X Terms, term : Terms]

MCTypeOK ==
    /\ currentTerm \in [MCServer -> MCTerms]
    /\ state \in [MCServer -> {Follower, Leader}]
    /\ log \in [MCServer -> MCLogs]
    /\ committed \subseteq [entry : (1..MaxLogLen) \X MCTerms, term : MCTerms]

\* Explicit length and term constraint to keep exploration finite.
StateConstraint ==
    /\ \A s \in MCServer : Len(log[s]) <= MaxLogLen
    /\ \A s \in MCServer : currentTerm[s] \in MCTerms

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

OnePrimaryPerTerm ==
    \A i, j \in Server :
        (/\ state[i] = Leader
         /\ state[j] = Leader
         /\ currentTerm[i] = currentTerm[j]) => i = j

LogMatching ==
    \A i, j \in Server :
        \A k \in 1..Max({0, Min({Len(log[i]), Len(log[j])})}) :
            log[i][k] = log[j][k] =>
                SubSeq(log[i], 1, k) = SubSeq(log[j], 1, k)

LeaderCompleteness ==
    \A c \in committed :
        \A i \in Server :
            (state[i] = Leader /\ currentTerm[i] > c.term) => InLog(c.entry, i)

StateMachineSafety ==
    \A c1, c2 \in committed :
        c1.entry[1] = c2.entry[1] => c1.entry = c2.entry

THEOREM Spec => [](TypeOK /\ OnePrimaryPerTerm /\ StateMachineSafety)
================================================================================