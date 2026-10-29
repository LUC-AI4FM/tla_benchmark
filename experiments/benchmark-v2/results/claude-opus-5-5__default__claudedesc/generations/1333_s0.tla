------------------------------- MODULE EWD998 -------------------------------
(***************************************************************************)
(* TLA+ specification of Shmuel Safra's algorithm for distributed          *)
(* termination detection on a ring of N nodes, as described in EWD 998.    *)
(*                                                                         *)
(* TLC configuration:                                                      *)
(*   CONSTANT N = 3                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTRAINT StateConstraint                                            *)
(*   INVARIANT TypeOK Inv TerminationDetection                             *)
(*   PROPERTY Liveness                                                     *)
(*   ALIAS Alias                                                           *)
(***************************************************************************)
EXTENDS Integers, Naturals, FiniteSets, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* activation status of each node
    color,    \* color of each node
    counter,  \* messages sent minus messages received, per node
    pending,  \* number of in-flight messages destined for each node
    token     \* token: position, cumulative counter q, color

vars == <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------
(* Helper operators *)

RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

Rng(a, b) == { i \in Node : a <= i /\ i <= b }

-----------------------------------------------------------------------------

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

-----------------------------------------------------------------------------
(* System actions *)

InitiateProbe ==
    /\ token.pos = 0
    /\ \* previous round was inconclusive
       \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q > 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

PassToken(i) ==
    /\ ~ active[i]
    /\ token.pos = i
    /\ token' = [token EXCEPT !.pos   = @ - 1,
                              !.q     = @ + counter[i],
                              !.color = IF color[i] = "black" THEN "black" ELSE @]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(* Environment actions *)

SendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color'   = [color EXCEPT ![i] = "black"]
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<token>>

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* State constraint for model checking *)

StateConstraint ==
    /\ \A i \in Node : counter[i] <= 3 /\ pending[i] <= 3
    /\ token.q <= 9

-----------------------------------------------------------------------------
(* Safra's inductive invariant *)

B == Sum(pending, Node)

Inv ==
    /\ B = Sum(counter, Node)
    /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
          /\ IF token.pos = N-1
                THEN token.q = 0
                ELSE token.q = Sum(counter, Rng(token.pos + 1, N-1))
       \/ Sum(counter, Rng(0, token.pos)) + token.q > 0
       \/ \E i \in Rng(0, token.pos) : color[i] = "black"
       \/ token.color = "black"

-----------------------------------------------------------------------------
(* Correctness properties *)

terminated ==
    \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

TerminationDetection == terminationDetected => terminated

Liveness == terminated ~> terminationDetected

-----------------------------------------------------------------------------
(* TLC instrumentation *)

Alias ==
    [ active      |-> active,
      color       |-> color,
      counter     |-> counter,
      pending     |-> pending,
      token       |-> token,
      level       |-> TLCGet("level"),
      tokenPasses |-> IF token.pos = 0 THEN N - 1 ELSE (N - 1) - token.pos,
      activeNodes |-> { i \in Node : active[i] },
      inactiveNodes |-> { i \in Node : ~ active[i] },
      tokenStats  |-> [ pos   |-> token.pos,
                        q     |-> token.q,
                        color |-> token.color,
                        sumQ  |-> token.q + counter[token.pos] ],
      inFlight    |-> B,
      terminated  |-> terminated,
      detected    |-> terminationDetected ]

=============================================================================