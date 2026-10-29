------------------------------- MODULE EWD998PCal -------------------------------
(***************************************************************************)
(* Safra's distributed termination detection algorithm (EWD 998) on a     *)
(* ring of N nodes.  The network is modeled as a bag of messages per node, *)
(* carrying payload messages and a single circulating token with fields q  *)
(* and color.                                                              *)
(***************************************************************************)
EXTENDS Integers, Bags, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node      == 0 .. N-1
Initiator == 0
Color     == {"white", "black"}

PayloadMsg == [type |-> "pl"]
TokenMsgs  == [type : {"tok"}, q : Int, color : Color]

(***************************************************************************
--algorithm ewd998 {
  variables
    active  \in [Node -> BOOLEAN],
    color   \in [Node -> Color],
    counter = [i \in Node |-> 0],
    network = [i \in Node |->
                 IF i = Initiator
                 THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                 ELSE EmptyBag];

  fair process (node \in Node) {
    l: while (TRUE) {
         either {  \* send a payload message
           await active[self];
           with (to \in Node \ {self}) {
             network[to] := network[to] (+) SetToBag({[type |-> "pl"]})
           };
           counter[self] := counter[self] + 1
         } or {    \* receive a payload message
           with (msg \in {m \in BagToSet(network[self]) : m.type = "pl"}) {
             counter[self] := counter[self] - 1;
             active[self]  := TRUE;
             color[self]   := "black";
             network[self] := network[self] (-) SetToBag({msg})
           }
         } or {    \* become inactive
           active[self] := FALSE
         } or {    \* pass the token
           await self # Initiator /\ ~active[self];
           with (tok \in {m \in BagToSet(network[self]) : m.type = "tok"}) {
             network[self] := network[self] (-) SetToBag({tok}) ||
             network[self-1] := network[self-1] (+)
                 SetToBag({[type |-> "tok", q |-> tok.q + counter[self],
                            color |-> IF color[self] = "black"
                                      THEN "black" ELSE tok.color]})
           };
           color[self] := "white"
         } or {    \* initiator restarts token round
           await self = Initiator /\ ~active[self];
           with (tok \in {m \in BagToSet(network[self]) : m.type = "tok"}) {
             await tok.color = "black" \/ color[self] = "black"
                   \/ tok.q + counter[self] # 0;
             network[self] := network[self] (-) SetToBag({tok}) ||
             network[N-1]  := network[N-1] (+)
                 SetToBag({[type |-> "tok", q |-> 0, color |-> "white"]})
           };
           color[self] := "white"
         }
    }
  }
}
***************************************************************************)

VARIABLES active, color, counter, network

vars == << active, color, counter, network >>

-----------------------------------------------------------------------------

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ network = [i \in Node |->
                    IF i = Initiator
                    THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                    ELSE EmptyBag]

SendMsg(self) ==
    /\ active[self]
    /\ \E to \in Node \ {self}:
         network' = [network EXCEPT ![to] = @ (+) SetToBag({PayloadMsg})]
    /\ counter' = [counter EXCEPT ![self] = @ + 1]
    /\ UNCHANGED << active, color >>

RecvMsg(self) ==
    /\ \E msg \in {m \in BagToSet(network[self]) : m.type = "pl"}:
         /\ counter' = [counter EXCEPT ![self] = @ - 1]
         /\ active'  = [active EXCEPT ![self] = TRUE]
         /\ color'   = [color EXCEPT ![self] = "black"]
         /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({msg})]

Deactivate(self) ==
    /\ active' = [active EXCEPT ![self] = FALSE]
    /\ UNCHANGED << color, counter, network >>

PassToken(self) ==
    /\ self # Initiator
    /\ ~ active[self]
    /\ \E tok \in {m \in BagToSet(network[self]) : m.type = "tok"}:
         network' = [network EXCEPT
                       ![self]   = @ (-) SetToBag({tok}),
                       ![self-1] = @ (+) SetToBag({[type  |-> "tok",
                                                    q     |-> tok.q + counter[self],
                                                    color |-> IF color[self] = "black"
                                                              THEN "black"
                                                              ELSE tok.color]})]
    /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << active, counter >>

InitiateToken(self) ==
    /\ self = Initiator
    /\ ~ active[self]
    /\ \E tok \in {m \in BagToSet(network[self]) : m.type = "tok"}:
         /\ \/ tok.color = "black"
            \/ color[self] = "black"
            \/ tok.q + counter[self] # 0
         /\ network' = [network EXCEPT
                          ![self] = @ (-) SetToBag({tok}),
                          ![N-1]  = @ (+) SetToBag({[type  |-> "tok",
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

Next == \E self \in Node: node(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Node:
         /\ WF_vars(SendMsg(self))
         /\ WF_vars(RecvMsg(self))
         /\ WF_vars(Deactivate(self))
         /\ WF_vars(PassToken(self))
         /\ WF_vars(InitiateToken(self))

-----------------------------------------------------------------------------
(* Helper definitions *)

PendingCount(i) == CopiesIn(PayloadMsg, network[i])

TokenHolder == CHOOSE i \in Node : \E m \in BagToSet(network[i]) : m.type = "tok"

TheToken == CHOOSE m \in BagToSet(network[TokenHolder]) : m.type = "tok"

TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ \A i \in Node : IsABag(network[i])
    /\ \A i \in Node : BagToSet(network[i]) \subseteq ({PayloadMsg} \cup TokenMsgs)
    /\ Cardinality({i \in Node : \E m \in BagToSet(network[i]) : m.type = "tok"}) = 1

Terminated ==
    \A i \in Node : ~ active[i] /\ PendingCount(i) = 0

terminationDetected ==
    \E tok \in BagToSet(network[Initiator]) :
        /\ tok.type = "tok"
        /\ tok.color = "white"
        /\ tok.q + counter[Initiator] = 0
        /\ color[Initiator] = "white"
        /\ ~ active[Initiator]

(* Safety: termination is only detected if the system has terminated *)
Safety == terminationDetected => Terminated

(* Liveness: termination is eventually detected *)
Liveness == Terminated ~> terminationDetected

-----------------------------------------------------------------------------
(* Refinement-style comparison with EWD998 *)

EWD998 == INSTANCE EWD998 WITH
            active  <- active,
            color   <- color,
            counter <- counter,
            pending <- [i \in Node |-> PendingCount(i)],
            token   <- [pos   |-> TokenHolder,
                        q     |-> TheToken.q,
                        color |-> TheToken.color]

EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec

-----------------------------------------------------------------------------
(* State constraint bounding counters for model checking *)

StateConstraint ==
    \A i \in Node :
        /\ counter[i] \in -3 .. 3
        /\ PendingCount(i) <= 3

=============================================================================