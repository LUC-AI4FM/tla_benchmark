---------------------------- MODULE SafraTermination ----------------------------
(***************************************************************************)
(* Safra's token-based termination detection algorithm (EWD998) for N     *)
(* processes arranged in a unidirectional ring.                            *)
(*                                                                         *)
(* Process 0 is the initiator. The token travels 0 -> N-1 -> ... -> 1 -> 0. *)
(* Each process i keeps:                                                   *)
(*   active[i]  - whether it is active                                     *)
(*   color[i]   - "white"/"black"; it records whether the process sent or  *)
(*                received payload since it last forwarded the token       *)
(*   counter[i] - number of payload messages sent minus received           *)
(* pending[i] counts the payload messages in transit to process i.         *)
(* The single token is a message record: its position, its accumulated     *)
(* counter sum q, and its color.                                           *)
(***************************************************************************)
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,              \* [Node -> BOOLEAN]
    color,               \* [Node -> Color]
    counter,             \* [Node -> Int]
    pending,             \* [Node -> Nat], payload messages in transit to node
    token,               \* [pos : Node, q : Int, color : Color]
    terminationDetected  \* BOOLEAN

vars == <<active, color, counter, pending, token, terminationDetected>>

-----------------------------------------------------------------------------
(* Helper operators *)

RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + SumF(f, S \ {x})

Rng(a, b) == {i \in Int : a <= i /\ i <= b}

-----------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ pending \in [Node -> Nat]
    /\ token \in [pos : Node, q : Int, color : Color]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pending = [i \in Node |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
    /\ terminationDetected = FALSE

-----------------------------------------------------------------------------
(* Token actions *)

(* The initiator, holding the token while inactive, starts a new round  *)
(* because the previous round was inconclusive.                         *)
InitiateProbe ==
    /\ token.pos = 0
    /\ ~active[0]
    /\ ~terminationDetected
    /\ \/ token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + token.q # 0
    /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pending, terminationDetected>>

(* An inactive non-initiator process forwards the token, adding its    *)
(* counter and blackening the token if it is itself black.             *)
PassToken(i) ==
    /\ i # 0
    /\ token.pos = i
    /\ ~active[i]
    /\ token' = [pos   |-> i - 1,
                 q     |-> token.q + counter[i],
                 color |-> IF color[i] = "black" THEN "black" ELSE token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pending, terminationDetected>>

(* The initiator, inactive and holding a white token from a full round, *)
(* with white color and zero global count, declares termination.        *)
DetectTermination ==
    /\ token.pos = 0
    /\ ~active[0]
    /\ ~terminationDetected
    /\ token.color = "white"
    /\ color[0] = "white"
    /\ counter[0] + token.q = 0
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, color, counter, pending, token>>

-----------------------------------------------------------------------------
(* System (payload) actions *)

SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node :
          pending' = [pending EXCEPT ![j] = @ + 1]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ color' = [color EXCEPT ![i] = "black"]   \* sender records it sent work
    /\ UNCHANGED <<active, token, terminationDetected>>

RecvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ color' = [color EXCEPT ![i] = "black"]   \* Safra: receipt blackens
    /\ UNCHANGED <<token, terminationDetected>>

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pending, token, terminationDetected>>

-----------------------------------------------------------------------------
System(i)  == SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Detection == InitiateProbe \/ DetectTermination \/ \E i \in Node \ {0} : PassToken(i)

Next == Detection \/ \E i \in Node : System(i)

Fairness ==
    /\ WF_vars(InitiateProbe)
    /\ WF_vars(DetectTermination)
    /\ \A i \in Node \ {0} : WF_vars(PassToken(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

Terminated == \A i \in Node : ~active[i] /\ pending[i] = 0

(* Safety: termination is never declared prematurely. *)
TerminationDetectedOnlyIfTerminated ==
    terminationDetected => Terminated

(* Exactly one token exists: it is a single record located at one node. *)
AtMostOneToken == token.pos \in Node /\ Cardinality({token.pos}) = 1

(* Conservation: sum of local counters equals the number of in-flight messages. *)
CounterConservation == SumF(counter, Node) = SumF(pending, Node)

(* Safra's main invariant: token metadata accumulates exactly the counters *)
(* of the processes it has visited in this round, unless the round is       *)
(* already known to be inconclusive.                                        *)
SafraInv ==
    /\ CounterConservation
    /\ \/ /\ \A i \in Rng(token.pos + 1, N - 1) : ~active[i]
          /\ token.q = SumF(counter, Rng(token.pos + 1, N - 1))
       \/ SumF(counter, Rng(0, token.pos)) + token.q > 0
       \/ \E i \in Rng(0, token.pos) : color[i] = "black"
       \/ token.color = "black"

Inv ==
    /\ TypeOK
    /\ AtMostOneToken
    /\ CounterConservation
    /\ SafraInv
    /\ TerminationDetectedOnlyIfTerminated

(* Monotonicity of token metadata within a round: a black token stays     *)
(* black, and q only changes by adding the forwarding node's counter.     *)
TokenMonotone ==
    [][ (token.pos # 0 /\ token'.pos = token.pos - 1) =>
           /\ (token.color = "black" => token'.color = "black")
           /\ token'.q = token.q + counter[token.pos] ]_vars

(* Once declared, termination remains declared. *)
DetectionStable == [][terminationDetected => terminationDetected']_vars

(* Liveness: quiescence eventually leads to detection. *)
Liveness == Terminated ~> terminationDetected

THEOREM Spec => []Inv
THEOREM Spec => TokenMonotone /\ DetectionStable
THEOREM Spec => Liveness
=============================================================================