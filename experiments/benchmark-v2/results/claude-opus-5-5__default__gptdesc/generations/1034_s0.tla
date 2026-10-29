---------------------------- MODULE SailfishBounded ----------------------------
(***************************************************************************)
(* A small bounded configuration of the Sailfish DAG-based BFT protocol.   *)
(* There are three nodes, and one of them (n3) is Byzantine.               *)
(* Correct nodes advance through DAG rounds and commit leader vertices.    *)
(* A state constraint bounds the rounds of correct nodes. A terminating    *)
(* variant of the spec lets behaviors stutter once every correct node has  *)
(* finished. Several deliberately false predicates are included so that    *)
(* TLC produces interesting counterexample executions.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS n1, n2, n3      \* model values for the three nodes

CONSTANTS MaxRound        \* bound on rounds explored by non-faulty nodes

-----------------------------------------------------------------------------
(* Concrete node sets *)
N == {n1, n2, n3}         \* all nodes
F == {n3}                 \* Byzantine (faulty) nodes
P == N \ F                \* correct (non-faulty) nodes

(* Quorums and blocking sets: n = 3 and f = 1 *)
IsQuorum(Q)   == Q \subseteq N /\ Cardinality(Q) >= 2
IsBlocking(B) == B \subseteq N /\ Cardinality(B) >= 1 /\ B \cap P # {}

(* Round-robin leader schedule *)
Leader(r) == CASE r % 3 = 0 -> n1
               [] r % 3 = 1 -> n2
               [] OTHER     -> n3

(* Global stabilization time *)
GST == 2

-----------------------------------------------------------------------------
VARIABLES
    round,   \* round[p]: current DAG round of correct node p
    vs,      \* the set of DAG vertices broadcast so far
    log,     \* log[p]: sequence of committed leader rounds at correct node p
    clock    \* global time, used to model GST

vars == <<round, vs, log, clock>>

Vertex == [src : N, rnd : 0..(MaxRound + 1), preds : SUBSET N]

HasVertex(n, r) == \E v \in vs : v.src = n /\ v.rnd = r

TypeOK ==
    /\ round \in [P -> Nat]
    /\ vs \subseteq Vertex
    /\ log \in [P -> Seq(Nat)]
    /\ clock \in 0..GST

-----------------------------------------------------------------------------
Init ==
    /\ round = [p \in P |-> 0]
    /\ vs = {[src |-> n, rnd |-> 0, preds |-> {}] : n \in N}
    /\ log = [p \in P |-> << >>]
    /\ clock = 0

(* Time advances until GST is reached *)
Tick ==
    /\ clock < GST
    /\ clock' = clock + 1
    /\ UNCHANGED <<round, vs, log>>

(* A correct node moves to round r+1 once it has a quorum of round-r       *)
(* vertices. After GST it also waits for the round-r leader vertex.       *)
Advance(p) ==
    LET r == round[p] IN
    /\ \E Q \in SUBSET N :
         /\ IsQuorum(Q)
         /\ \A q \in Q : HasVertex(q, r)
         /\ (clock < GST \/ Leader(r) \in Q)
         /\ vs' = vs \cup {[src |-> p, rnd |-> r + 1, preds |-> Q]}
    /\ round' = [round EXCEPT ![p] = r + 1]
    /\ UNCHANGED <<log, clock>>

(* A Byzantine node may broadcast arbitrary (even equivocating) vertices. *)
ByzVertex(b) ==
    /\ \E r \in 1..(MaxRound + 1), Q \in SUBSET N :
         /\ \A q \in Q : HasVertex(q, r - 1)
         /\ LET v == [src |-> b, rnd |-> r, preds |-> Q] IN
              /\ v \notin vs
              /\ vs' = vs \cup {v}
    /\ UNCHANGED <<round, log, clock>>

(* Round-(r+1) votes for the round-r leader vertex *)
Votes(r) == { v.src : v \in { w \in vs : w.rnd = r + 1 /\ Leader(r) \in w.preds } }

(* A correct node directly commits the leader vertex of round r *)
Commit(p) ==
    /\ \E r \in 0..MaxRound :
         /\ r < round[p]
         /\ HasVertex(Leader(r), r)
         /\ IsQuorum(Votes(r))
         /\ (log[p] = << >> \/ r > log[p][Len(log[p])])
         /\ log' = [log EXCEPT ![p] = Append(@, r)]
    /\ UNCHANGED <<round, vs, clock>>

Next ==
    \/ Tick
    \/ \E p \in P : Advance(p) \/ Commit(p)
    \/ \E b \in F : ByzVertex(b)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A p \in P : WF_vars(Advance(p)) /\ WF_vars(Commit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Bound explored rounds for non-faulty nodes *)
StateConstraint == \A p \in P : round[p] <= MaxRound

(* Terminating variant: once all correct nodes finish, the system stutters *)
AllCorrectFinished == \A p \in P : round[p] >= MaxRound

Terminate == AllCorrectFinished /\ UNCHANGED vars

TerminatingNext ==
    \/ (~AllCorrectFinished /\ Next)
    \/ Terminate

TerminatingSpec == Init /\ [][TerminatingNext]_vars /\ WF_vars(TerminatingNext)

-----------------------------------------------------------------------------
(* Safety: correct nodes' logs are prefix-consistent *)
IsPrefix(s, t) == Len(s) <= Len(t) /\ \A i \in 1..Len(s) : s[i] = t[i]

Consistency ==
    \A p, q \in P : IsPrefix(log[p], log[q]) \/ IsPrefix(log[q], log[p])

(* Logs are strictly increasing in round *)
LogMonotonic ==
    \A p \in P : \A i, j \in 1..Len(log[p]) : i < j => log[p][i] < log[p][j]

(* Liveness: eventually all correct nodes finish *)
EventuallyAllFinished == <>AllCorrectFinished

-----------------------------------------------------------------------------
(* Deliberately false predicates: TLC checks these to produce example executions. *)

(* False invariant: the correct nodes never all finish *)
NotAllCorrectFinished == ~AllCorrectFinished

(* False temporal property: the correct nodes never all finish *)
NeverAllFinish == []~AllCorrectFinished

(* False invariant: no correct node ever commits a log entry *)
NoCommit == \A p \in P : log[p] = << >>

(* False invariant: the logs of correct nodes never get past one entry *)
LogShort == \A p \in P : Len(log[p]) < 2

(* False temporal property: no correct node ever has a committed entry *)
NeverCommit == [](\A p \in P : Len(log[p]) = 0)

(* False invariant: no correct node finishes with a non-empty log *)
NoFinishWithCommit ==
    ~(AllCorrectFinished /\ \A p \in P : Len(log[p]) > 0)

=============================================================================