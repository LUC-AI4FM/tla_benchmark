------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* Safra's algorithm for distributed termination detection on a ring      *)
(* (EWD 998).  The network is modeled as a bag of in-flight payload        *)
(* messages per node (pending counts), which permits arbitrary reordering  *)
(* and delay but no loss.                                                  *)
(***************************************************************************)
EXTENDS Naturals, Integers

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"white", "black"}
Initiator == 0

VARIABLES
  active,   \* activation status of nodes
  color,    \* color of nodes
  counter,  \* (#messages sent) - (#messages received) per node
  pending,  \* number of payload messages in transit to each node
  token     \* the token: position, accumulated counter, color

vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in [pos : Node, q : Int, color : Color]

---------------------------------------------------------------------------

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> Initiator, q |-> 0, color |-> "black"]

(* The initiator starts a new round when the previous one was inconclusive. *)
InitiateProbe ==
  /\ token.pos = Initiator
  /\ \/ token.color = "black"
     \/ color[Initiator] = "black"
     \/ counter[Initiator] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![Initiator] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

(* An inactive non-initiator node passes the token to its predecessor.     *)
PassToken(i) ==
  /\ i # Initiator
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> i - 1,
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {Initiator} : PassToken(i)

---------------------------------------------------------------------------

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        pending' = [pending EXCEPT ![j] = @ + 1]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED token

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

---------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

EWD998Spec == Spec

---------------------------------------------------------------------------

terminationDetected ==
  /\ token.pos = Initiator
  /\ token.color = "white"
  /\ token.q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

Termination == \A i \in Node : ~ active[i] /\ pending[i] = 0

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE x \in S : TRUE
                  IN f[x] + Sum(f, S \ {x})

Rng(a, b) == {i \in Node : a <= i /\ i <= b}

(* Safra's main inductive invariant. *)
Inv ==
  /\ Sum(pending, Node) = Sum(counter, Node)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : ~ active[i]
        /\ IF token.pos = N-1 THEN token.q = 0
           ELSE token.q = Sum(counter, Rng(token.pos + 1, N-1))
     \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

Safe == [](terminationDetected => Termination)

Live == Termination ~> terminationDetected

---------------------------------------------------------------------------

MaxCounter == 3

StateConstraint ==
  /\ \A i \in Node : counter[i] <= MaxCounter /\ pending[i] <= MaxCounter
  /\ token.q <= MaxCounter * N
  /\ token.q >= -(MaxCounter * N)

Alias ==
  [ active              |-> active,
    color               |-> color,
    counter             |-> counter,
    pending             |-> pending,
    token               |-> token,
    terminationDetected |-> terminationDetected,
    termination         |-> Termination ]

=============================================================================