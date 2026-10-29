---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election on a unidirectional (clockwise) ring of   *)
(* N processes with unique numeric identities. Any subset of processes may *)
(* initiate the election concurrently. The smallest initiator identity     *)
(* wins.                                                                   *)
(*                                                                         *)
(* Communication is asynchronous. Each recipient has an unordered buffer   *)
(* of pending candidate messages. Every identity is sent exactly once by   *)
(* its owner and forwarded along the ring, so at most one copy of a given  *)
(* identity is ever in transit. A set therefore suffices as the buffer.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N,   \* number of processes on the ring
          Id   \* sequence of unique numeric identities, Id[i] for process i

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME IdAssumption ==
          /\ Id \in Seq(Nat)
          /\ Len(Id) = N
          /\ \A i, j \in 1..N : i # j => Id[i] # Id[j]

Procs == 1..N

\* Clockwise neighbour of process p
Succ(p) == IF p = N THEN 1 ELSE p + 1

\* Minimum of a nonempty set of naturals
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

IdSet == {Id[p] : p \in Procs}

VARIABLES
    status,     \* status[p] \in {"candidate", "lost", "won"}
    msgs,       \* msgs[p] : set of candidate IDs pending delivery to p
    initiator   \* history variable: set of processes that initiated

vars == <<status, msgs, initiator>>

TypeOK ==
    /\ status \in [Procs -> {"candidate", "lost", "won"}]
    /\ msgs \in [Procs -> SUBSET IdSet]
    /\ initiator \in SUBSET Procs

(***************************************************************************)
(* Initial state: an arbitrary subset of processes initiates. Each         *)
(* initiator is a candidate and has sent its own ID to its clockwise       *)
(* neighbour. Non-initiators never compete. They are "lost" from the start *)
(* and only forward messages.                                              *)
(***************************************************************************)
Init ==
    /\ initiator \in SUBSET Procs
    /\ status = [p \in Procs |->
                    IF p \in initiator THEN "candidate" ELSE "lost"]
    /\ msgs = [p \in Procs |->
                  {Id[q] : q \in {r \in initiator : Succ(r) = p}}]

\* Forward message m from p to its clockwise neighbour
Forward(p, m) ==
    msgs' = [msgs EXCEPT ![p] = @ \ {m},
                         ![Succ(p)] = @ \cup {m}]

\* Discard message m at p
Discard(p, m) ==
    msgs' = [msgs EXCEPT ![p] = @ \ {m}]

(***************************************************************************)
(* A step of process p: receive some pending candidate message m and act   *)
(* on it.                                                                  *)
(***************************************************************************)
Receive(p, m) ==
    /\ m \in msgs[p]
    /\ CASE m = Id[p] ->
              \* own ID came back: declare leadership
              /\ status' = [status EXCEPT ![p] = "won"]
              /\ Discard(p, m)
         [] m < Id[p] ->
              \* smaller ID: withdraw candidacy and forward
              /\ status' = [status EXCEPT ![p] =
                               IF @ = "candidate" THEN "lost" ELSE @]
              /\ Forward(p, m)
         [] m > Id[p] /\ status[p] = "lost" ->
              \* passive process relays larger IDs
              /\ UNCHANGED status
              /\ Forward(p, m)
         [] OTHER ->
              \* active (candidate or won) process swallows larger IDs
              /\ UNCHANGED status
              /\ Discard(p, m)
    /\ UNCHANGED initiator

Step(p) == \E m \in msgs[p] : Receive(p, m)

\* Quiescence: no messages remain. Stuttering here avoids spurious deadlock.
Terminated ==
    /\ \A p \in Procs : msgs[p] = {}
    /\ UNCHANGED vars

Next == (\E p \in Procs : Step(p)) \/ Terminated

\* Weak fairness for each process's step
Fairness == \A p \in Procs : WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

Leaders == {p \in Procs : status[p] = "won"}

\* Safety: a leader is an initiator holding the smallest initiator ID,
\* and every other process has lost.
LeaderSafety ==
    \A p \in Procs :
        status[p] = "won" =>
            /\ p \in initiator
            /\ Id[p] = MinOf({Id[q] : q \in initiator})
            /\ \A q \in Procs \ {p} : status[q] = "lost"

\* Uniqueness: at most one leader in any state.
Uniqueness == \A p, q \in Procs :
                  (status[p] = "won" /\ status[q] = "won") => p = q

\* Leadership is stable. Combined with Uniqueness, at most one process ever
\* declares itself leader over the whole behaviour.
LeaderStable ==
    \A p \in Procs : [](status[p] = "won" => [](status[p] = "won"))

\* The initiator set never changes after the initial state.
InitiatorsFixed ==
    [][initiator' = initiator]_vars

\* A lost process never becomes a candidate or leader again.
LostStable ==
    \A p \in Procs : [](status[p] = "lost" => [](status[p] = "lost"))

\* Termination / liveness: if there is an initiator, a leader eventually
\* emerges.
Termination ==
    (initiator # {}) => <>(\E p \in Procs : status[p] = "won")

\* Progress (no livelock): the election completes. Eventually exactly the
\* minimal initiator is leader, all other processes have lost, and no
\* messages remain in transit.
ElectionCompletes ==
    (initiator # {}) =>
        <>[]( /\ \E p \in Procs :
                    /\ status[p] = "won"
                    /\ Id[p] = MinOf({Id[q] : q \in initiator})
              /\ \A p \in Procs : msgs[p] = {} )

\* With no initiators nothing ever happens and nobody wins.
NoInitiatorNoLeader ==
    (initiator = {}) => [](Leaders = {})

THEOREM Spec => [](TypeOK /\ LeaderSafety /\ Uniqueness)
THEOREM Spec => LeaderStable /\ LostStable /\ InitiatorsFixed
THEOREM Spec => Termination /\ ElectionCompletes /\ NoInitiatorNoLeader
=============================================================================