------------------------------- MODULE MCAbstractRaft -------------------------------
(***************************************************************************)
(* Model-checking wrapper around an abstract Raft-style replication        *)
(* protocol. It fixes a concrete symmetric set of three servers, bounds    *)
(* terms to 2..4, starts every server at the minimum term, and bounds log  *)
(* lengths with bounded sequences plus an explicit length constraint.      *)
(* The abstraction is included inline so that the module is                *)
(* self-contained. Symmetry reduction permutes the server set.             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, n3          \* model values for the three servers

CONSTANTS Primary, Secondary  \* server states (model values)

-----------------------------------------------------------------------------
(* Configuration-style helper operators *)

MCServer == {n1, n2, n3}

MCTerms == 2..4

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

MCStartTerm == Min(MCTerms)

MCMaxTerm == Max(MCTerms)

MCMaxLogLen == 2

\* All sequences over S with length at most n.
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

\* Symmetry reduction over permutations of the server set.
MCSymmetry == Permutations(MCServer)

-----------------------------------------------------------------------------
(* Underlying abstraction *)

Server == MCServer

VARIABLES currentTerm, state, log

vars == <<currentTerm, state, log>>

Quorums == { Q \in SUBSET Server : Cardinality(Q) * 2 > Cardinality(Server) }

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

\* Server v may vote for server i in term newTerm.
CanVoteFor(v, i, newTerm) ==
    /\ currentTerm[v] < newTerm
    /\ \/ LastTerm(log[i]) > LastTerm(log[v])
       \/ /\ LastTerm(log[i]) = LastTerm(log[v])
          /\ Len(log[i]) >= Len(log[v])

\* Log of i is a prefix-compatible extension point of the log of j.
CanAppendFrom(i, j) ==
    /\ Len(log[j]) > Len(log[i])
    /\ \/ Len(log[i]) = 0
       \/ log[i][Len(log[i])] = log[j][Len(log[i])]

-----------------------------------------------------------------------------
(* Type constraints *)

TypeOK ==
    /\ currentTerm \in [Server -> MCTerms]
    /\ state \in [Server -> {Primary, Secondary}]
    /\ log \in [Server -> BoundedSeq(MCTerms, MCMaxLogLen)]

\* Explicit state constraint bounding log lengths and terms.
LogLenConstraint == \A s \in Server : Len(log[s]) <= MCMaxLogLen

TermConstraint == \A s \in Server : currentTerm[s] \in MCTerms

MCStateConstraint == LogLenConstraint /\ TermConstraint

-----------------------------------------------------------------------------
(* Initial state and actions *)

Init ==
    /\ currentTerm = [s \in Server |-> MCStartTerm]
    /\ state = [s \in Server |-> Secondary]
    /\ log = [s \in Server |-> << >>]

BecomeLeader(i, Q) ==
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in Q
    /\ newTerm \in MCTerms
    /\ \A v \in Q : CanVoteFor(v, i, newTerm)
    /\ currentTerm' = [s \in Server |-> IF s \in Q THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in Q THEN Secondary
                    ELSE state[s]]
    /\ UNCHANGED log

ClientRequest(i) ==
    /\ state[i] = Primary
    /\ Len(log[i]) < MCMaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state>>

GetEntries(i, j) ==
    /\ i # j
    /\ state[i] = Secondary
    /\ CanAppendFrom(i, j)
    /\ Len(log[i]) < MCMaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<currentTerm, state>>

RollbackEntries(i, j) ==
    /\ i # j
    /\ state[i] = Secondary
    /\ Len(log[i]) > 0
    /\ LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \/ log[i][Len(log[i])] # log[j][Len(log[i])]
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<currentTerm, state>>

UpdateTerms(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary]
    /\ UNCHANGED log

Next ==
    \/ \E i \in Server, Q \in Quorums : BecomeLeader(i, Q)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i, j \in Server : GetEntries(i, j)
    \/ \E i, j \in Server : RollbackEntries(i, j)
    \/ \E i, j \in Server : UpdateTerms(i, j)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

ElectionSafety ==
    \A s, t \in Server :
        (/\ state[s] = Primary
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => s = t

\* Terms in each log are monotonically non-decreasing.
LogTermsMonotonic ==
    \A s \in Server :
        \A k \in 1..(Len(log[s]) - 1) : log[s][k] <= log[s][k + 1]

\* No log entry carries a term greater than the server's current term.
LogTermsBounded ==
    \A s \in Server :
        \A k \in 1..Len(log[s]) : log[s][k] <= currentTerm[s]

THEOREM Spec => [](TypeOK /\ ElectionSafety /\ LogTermsMonotonic)
=============================================================================