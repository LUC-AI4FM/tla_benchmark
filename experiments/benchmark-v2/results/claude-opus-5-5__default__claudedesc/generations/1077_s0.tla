--------------------------- MODULE EWD998PCal ---------------------------
(***************************************************************************)
(* Shmuel Safra's distributed termination detection algorithm on a ring   *)
(* of N nodes, as described in EWD 998.  This is the TLA+ translation of   *)
(* the PlusCal algorithm "ewd998".  Node 0 is the initiator.  The network  *)
(* is modeled as a bag of messages per node.                               *)
(***************************************************************************)
EXTENDS Integers, Naturals, Sequences, Bags, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Initiator == 0
Color == {"white", "black"}

PlMsg == [type |-> "pl"]

VARIABLES network, active, color, counter

vars == << network, active, color, counter >>

---------------------------------------------------------------------------
(* Helper definitions (the PlusCal "define" block).                        *)

PendingMsgs(n) == IF PlMsg \in DOMAIN network[n]
                  THEN CopiesIn(PlMsg, network[n])
                  ELSE 0

HoldsToken(n) == \E m \in DOMAIN network[n] : m.type = "tok"

TokenMsgs == [type : {"tok"}, q : Int, color : Color]

TypeOK ==
    /\ \A n \in Node : IsABag(network[n])
    /\ \A n \in Node : \A m \in DOMAIN network[n] : m \in {PlMsg} \cup TokenMsgs
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]

---------------------------------------------------------------------------
Init ==
    /\ network = [n \in Node |->
                    IF n = Initiator
                    THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                    ELSE EmptyBag]
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [n \in Node |-> 0]

(* Send a payload message to some other node while active. *)
SendMsg(self) ==
    /\ active[self]
    /\ \E to \in Node \ {self} :
          network' = [network EXCEPT ![to] = @ (+) SetToBag({PlMsg})]
    /\ counter' = [counter EXCEPT ![self] = @ + 1]
    /\ UNCHANGED << active, color >>

(* Receive a payload message and become active. *)
RecvMsg(self) ==
    /\ PendingMsgs(self) > 0
    /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({PlMsg})]
    /\ counter' = [counter EXCEPT ![self] = @ - 1]
    /\ color' = [color EXCEPT ![self] = "black"]
    /\ active' = [active EXCEPT ![self] = TRUE]

(* Deactivate. *)
Deactivate(self) ==
    /\ active[self]
    /\ active' = [active EXCEPT ![self] = FALSE]
    /\ UNCHANGED << network, color, counter >>

(* Pass the token towards the initiator. *)
PassToken(self) ==
    /\ self # Initiator
    /\ ~ active[self]
    /\ \E tok \in DOMAIN network[self] :
          /\ tok.type = "tok"
          /\ network' = [network EXCEPT
                ![self]     = @ (-) SetToBag({tok}),
                ![self - 1] = @ (+) SetToBag({[type  |-> "tok",
                                               q     |-> tok.q + counter[self],
                                               color |-> IF color[self] = "black"
                                                         THEN "black"
                                                         ELSE tok.color]})]
          /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << active, counter >>

(* The initiator starts a new round if termination is not yet detected. *)
InitiateToken(self) ==
    /\ self = Initiator
    /\ ~ active[self]
    /\ \E tok \in DOMAIN network[self] :
          /\ tok.type = "tok"
          /\ ~ ( /\ tok.color = "white"
                 /\ color[self] = "white"
                 /\ tok.q + counter[self] = 0 )
          /\ network' = [network EXCEPT
                ![self]  = @ (-) SetToBag({tok}),
                ![N - 1] = @ (+) SetToBag({[type  |-> "tok",
                                            q     |-> 0,
                                            color |-> "white"]})]
          /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << active, counter >>

node(self) ==
    \/ SendMsg(self)
    \/ RecvMsg(self)
    \/ Deactivate(self)
    \/ PassToken(self)
    \/ InitiateToken(self)

Next == \E self \in Node : node(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

---------------------------------------------------------------------------
(* Model-checking aids. *)

StateConstraint == \A n \in Node : counter[n] < 3

token ==
    LET tpos == CHOOSE i \in Node : HoldsToken(i)
        tok  == CHOOSE m \in DOMAIN network[tpos] : m.type = "tok"
    IN [pos |-> tpos, q |-> tok.q, color |-> tok.color]

Alias ==
    [ network |-> network,
      active  |-> active,
      color   |-> color,
      counter |-> counter,
      tpos    |-> token.pos,
      pending |-> [n \in Node |-> PendingMsgs(n)] ]

---------------------------------------------------------------------------
(* Refinement mapping to the abstract EWD998 specification. *)

inbox ==
    [n \in Node |->
        (IF n = token.pos
         THEN << [type |-> "tok", q |-> token.q, color |-> token.color] >>
         ELSE << >>)
        \o [i \in 1 .. PendingMsgs(n) |-> PlMsg] ]

EWD998 == INSTANCE EWD998 WITH active  <- active,
                               color   <- color,
                               counter <- counter,
                               inbox   <- inbox

EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec
=============================================================================