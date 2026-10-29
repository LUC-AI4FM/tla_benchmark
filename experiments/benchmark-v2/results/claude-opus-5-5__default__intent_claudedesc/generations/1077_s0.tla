------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* Safra's algorithm for distributed termination detection on a ring      *)
(* (EWD 998).  N nodes are arranged in a ring; node 0 is the initiator.   *)
(* The token travels from node i to node i-1, and from node 0 the         *)
(* initiator starts a new round by sending it to node N-1.                *)
(* The network is unordered: messages in transit are kept as a per-node   *)
(* count of pending payload messages, so they may be received in any      *)
(* order. They may be delayed arbitrarily but are never lost.             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* active[i]  : node i is active
    color,    \* color[i]   : contamination state of node i
    counter,  \* counter[i] : messages sent minus messages received by i
    pending,  \* pending[i] : number of payload messages in transit to i
    token     \* the token: position, accumulated count and color

vars == << active, color, counter, pending, token >>

(***************************************************************************)
(* Sum of f[x] over all x in the finite set S.                             *)
(***************************************************************************)
Sum(f, S) ==
    LET s[T \in SUBSET S] ==
            IF T = {} THEN 0
            ELSE LET x == CHOOSE y \in T : TRUE
                 IN  f[x] + s[T \ {x}]
    IN  s[S]

TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ pending \in [Node -> Nat]
    /\ token   \in [pos : Node, q : Int, color : Color]

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pending = [i \in Node |-> 0]
    /\ token   = [pos |-> 0, q |-> 0, color |-> "black"]

(***************************************************************************)
(* The initiator starts a new round when the token has returned and the   *)
(* last round was inconclusive.                                           *)
(***************************************************************************)
InitiateProbe ==
    /\ token.pos = 0
    /\ \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q > 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, counter, pending >>

(***************************************************************************)
(* An inactive node other than the initiator passes the token to its      *)
(* predecessor. It adds its counter to the token and taints the token if  *)
(* the node is black. The node then becomes white.                        *)
(***************************************************************************)
PassToken(i) ==
    /\ i # 0
    /\ ~ active[i]
    /\ token.pos = i
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED << active, counter, pending >>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

(***************************************************************************)
(* Actions of the underlying computation.                                 *)
(***************************************************************************)
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node \ {i} :
          /\ pending' = [pending EXCEPT ![j] = @ + 1]
          /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ UNCHANGED << active, color, token >>

RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ active'  = [active  EXCEPT ![i] = TRUE]
    /\ color'   = [color   EXCEPT ![i] = "black"]
    /\ UNCHANGED << token >>

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << color, counter, pending, token >>

Environment ==
    \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Fairness ==
    /\ WF_vars(InitiateProbe)
    /\ \A i \in Node \ {0} : WF_vars(PassToken(i))
    /\ \A i \in Node : WF_vars(RecvMsg(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Global termination: every node is inactive and no message is in transit.
Termination ==
    \A i \in Node : ~ active[i] /\ pending[i] = 0

\* The initiator announces termination.
terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

\* Safety: termination is never falsely detected.
TerminationDetection ==
    terminationDetected => Termination

\* Auxiliary invariant: the counters account exactly for messages in transit.
CounterInv ==
    Sum(counter, Node) = Sum(pending, Node)

\* Safra's inductive invariant (from EWD 998).
Rng(a, b) == { i \in Node : a <= i /\ i <= b }

SafraInv ==
    \/ /\ \A i \in Rng(token.pos + 1, N-1) : ~ active[i]
       /\ token.q = Sum(counter, Rng(token.pos + 1, N-1))
    \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
    \/ \E i \in Rng(0, token.pos) : color[i] = "black"
    \/ token.color = "black"

\* Liveness: once termination holds, it is eventually detected.
Liveness ==
    Termination ~> terminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================