------------------------------- MODULE SafraTermination -------------------------------
(***************************************************************************)
(* Safra's distributed termination-detection algorithm (EWD 998).         *)
(*                                                                         *)
(* N processes, numbered 0..N-1, form a unidirectional logical ring. The  *)
(* token travels from node i to node i-1, and from node 0 the initiator   *)
(* restarts a probe by sending it to node N-1.                             *)
(*                                                                         *)
(*  - Each process is active or passive and has a color, white or black.   *)
(*  - counter[i] = (#messages sent by i) - (#messages received by i).      *)
(*  - pending[i] = number of application messages in flight to i.          *)
(*  - The token record has three fields:                                   *)
(*      pos   : the node currently holding the token                       *)
(*      q     : sum of the counters of the nodes the token has visited     *)
(*              in this round (the suffix pos+1..N-1 of the ring)          *)
(*      color : white or black                                             *)
(*                                                                         *)
(* Assumptions                                                             *)
(*  - N is finite and N >= 1.                                              *)
(*  - Counters and in-flight message counts are unbounded integers in      *)
(*    principle.                                                           *)
(*  - For model checking, MaxCounter caps the number of unreceived         *)
(*    messages a node may have outstanding: send is enabled only while     *)
(*    counter[i] < MaxCounter. Because Sum(counter) = Sum(pending) >= 0,   *)
(*    this guard also bounds every counter from below by                   *)
(*    -(N-1)*MaxCounter and bounds every pending[i]. The state space is    *)
(*    therefore finite. The guard only restricts behaviors, so the safety  *)
(*    and inductive-invariant results do not depend on it.                 *)
(*  - StateConstraint is an optional extra bound for safety-only runs.     *)
(*  - Once termination is detected, no action is enabled. Run TLC with     *)
(*    deadlock checking disabled.                                          *)
(***************************************************************************)
EXTENDS Integers, Naturals

CONSTANTS N,           \* number of processes in the ring
          MaxCounter   \* model-checking bound on outstanding sends per node

ASSUME NAssumption   == N \in Nat \ {0}
ASSUME BoundAssumption == MaxCounter \in Nat \ {0}

Node      == 0 .. N-1
Initiator == 0
Color     == {"white", "black"}

VARIABLES
    active,    \* active[i] : TRUE iff process i is active
    color,     \* color[i]  : color of process i
    counter,   \* counter[i]: messages sent minus messages received by i
    pending,   \* pending[i]: application messages in transit to i
    token      \* [pos, q, color]

vars == <<active, color, counter, pending, token>>

(***************************************************************************)
(* Sum of f[x] for x in a finite set S.                                    *)
(***************************************************************************)
RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + SumF(f, S \ {x})

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ pending \in [Node -> Nat]
    /\ token   \in [pos : Node, q : Int, color : Color]

(***************************************************************************)
(* Initial states                                                          *)
(*                                                                         *)
(* Activity and colors are arbitrary. No messages are in flight. The      *)
(* token starts black at the initiator, so a fresh probe must be started  *)
(* before termination can be claimed.                                      *)
(***************************************************************************)
Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pending = [i \in Node |-> 0]
    /\ token   = [pos |-> Initiator, q |-> 0, color |-> "black"]

(***************************************************************************)
(* Detection condition observed by the initiator                           *)
(***************************************************************************)
TerminationDetected ==
    /\ token.pos = Initiator
    /\ token.color = "white"
    /\ token.q + counter[Initiator] = 0
    /\ color[Initiator] = "white"
    /\ ~ active[Initiator]

(***************************************************************************)
(* Token-related actions                                                   *)
(***************************************************************************)

(* The initiator starts a new probe round when the previous round failed. *)
InitiateProbe ==
    /\ token.pos = Initiator
    /\ \/ token.color = "black"
       \/ color[Initiator] = "black"
       \/ counter[Initiator] + token.q /= 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![Initiator] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

(* A passive non-initiator node i forwards the token to node i-1.         *)
(* It adds its counter to q, blackens the token if i is black, and then    *)
(* turns i white.                                                          *)
PassToken(i) ==
    /\ i /= Initiator
    /\ token.pos = i
    /\ ~ active[i]
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

(***************************************************************************)
(* Application (environment) actions                                       *)
(***************************************************************************)

(* An active node i sends a message to some node j. *)
SendMsg(i) ==
    /\ active[i]
    /\ counter[i] < MaxCounter            \* model-checking bound
    /\ \E j \in Node \ {i} :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

(* Node i receives a message. It becomes active and turns black. *)
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ active'  = [active  EXCEPT ![i] = TRUE]
    /\ color'   = [color   EXCEPT ![i] = "black"]
    /\ UNCHANGED token

(* An active node i becomes passive at an arbitrary time. *)
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
System ==
    \/ InitiateProbe
    \/ \E i \in Node \ {Initiator} : PassToken(i)

Environment ==
    \E i \in Node :
        \/ SendMsg(i)
        \/ RecvMsg(i)
        \/ Deactivate(i)

Next == System \/ Environment

(* Weak fairness on the detection protocol only. The application is not   *)
(* forced to make progress.                                                *)
Fairness == WF_vars(System)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Global termination                                                      *)
(***************************************************************************)
Terminated ==
    /\ \A i \in Node : ~ active[i]
    /\ \A i \in Node : pending[i] = 0

(***************************************************************************)
(* Safety: detection soundness                                             *)
(***************************************************************************)
TerminationDetectionSound == TerminationDetected => Terminated

Safety == []TerminationDetectionSound

(***************************************************************************)
(* Inductive invariant (Safra's reasoning, EWD 998)                        *)
(*                                                                         *)
(* Let B be the number of messages in flight. Then:                        *)
(*  P0: B = sum of all counters.                                           *)
(* In addition, at least one of the following holds:                       *)
(*  P1: all nodes the token has visited (pos+1..N-1) are passive, and q    *)
(*      is the sum of their counters.                                      *)
(*  P2: sum of counters of unvisited nodes 0..pos, plus q, is > 0.         *)
(*  P3: some unvisited node 0..pos is black.                               *)
(*  P4: the token is black.                                                *)
(***************************************************************************)
B == SumF(pending, Node)

Visited   == (token.pos + 1) .. (N - 1)
Unvisited == 0 .. token.pos

P0 == B = SumF(counter, Node)
P1 == /\ \A i \in Visited : ~ active[i]
      /\ token.q = SumF(counter, Visited)
P2 == SumF(counter, Unvisited) + token.q > 0
P3 == \E i \in Unvisited : color[i] = "black"
P4 == token.color = "black"

Inv ==
    /\ TypeOK
    /\ P0
    /\ (P1 \/ P2 \/ P3 \/ P4)

(***************************************************************************)
(* Liveness: once the system has terminated, the initiator eventually     *)
(* detects it.                                                             *)
(***************************************************************************)
Liveness == Terminated ~> TerminationDetected

(* Termination is stable. *)
TerminationStable == [][Terminated => Terminated']_vars

(***************************************************************************)
(* Optional state constraint for safety-only model checking               *)
(***************************************************************************)
StateConstraint ==
    /\ \A i \in Node : counter[i] \in -(N * MaxCounter) .. MaxCounter
    /\ \A i \in Node : pending[i] <= N * MaxCounter

(***************************************************************************)
(* Theorems (proof obligations)                                            *)
(***************************************************************************)
THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM InvInductive     == Inv /\ [Next]_vars => Inv'
THEOREM InvInit          == Init => Inv
THEOREM InvImpliesSafety == Inv => TerminationDetectionSound
THEOREM SpecSafety       == Spec => Safety
THEOREM SpecStable       == Spec => TerminationStable
THEOREM SpecLiveness     == Spec => Liveness
=============================================================================