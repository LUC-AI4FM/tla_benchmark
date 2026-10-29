------------------------------- MODULE EWD998PCal -------------------------------
(***************************************************************************)
(* Shmuel Safra's termination detection algorithm on a ring of N nodes,   *)
(* as described in Dijkstra's EWD 998.  The network is modeled as a bag   *)
(* of messages per node.  Messages are either payload messages ("pl") or  *)
(* the single token message ("tok").                                       *)
(***************************************************************************)
EXTENDS Integers, Bags, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Initiator == 0
Color == {"white", "black"}

BagAdd(B, x)    == B (+) SetToBag({x})
BagRemove(B, x) == B (-) SetToBag({x})

(* --algorithm ewd998 {
  variables
    network = [n \in Node |-> IF n = Initiator
                                THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                                ELSE EmptyBag];
    active \in [Node -> BOOLEAN];
    color \in [Node -> Color];
    counter = [n \in Node |-> 0];

  fair process (node \in Node) {
    l: while (TRUE) {
         either {  \* send payload message
            await active[self];
            with (to \in Node \ {self}) {
               network[to] := BagAdd(network[to], [type |-> "pl"]);
            };
            counter[self] := counter[self] + 1
         } or {    \* receive payload message
            with (msg \in DOMAIN network[self]) {
               await msg.type = "pl";
               counter[self] := counter[self] - 1;
               active[self] := TRUE;
               color[self] := "black";
               network[self] := BagRemove(network[self], msg)
            }
         } or {    \* deactivate
            await active[self];
            active[self] := FALSE
         } or {    \* pass token
            await self # Initiator;
            with (tok \in DOMAIN network[self]) {
               await tok.type = "tok" /\ ~active[self];
               network := [network EXCEPT
                  ![self-1] = BagAdd(@, [type |-> "tok", q |-> tok.q + counter[self],
                                         color |-> IF color[self] = "black" THEN "black" ELSE tok.color]),
                  ![self] = BagRemove(@, tok)];
               color[self] := "white"
            }
         } or {    \* initiate token
            await self = Initiator;
            with (tok \in DOMAIN network[self]) {
               await tok.type = "tok" /\
                     (color[self] = "black" \/ tok.q + counter[self] > 0 \/ tok.color = "black");
               network := [network EXCEPT
                  ![N-1] = BagAdd(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                  ![self] = BagRemove(@, tok)];
               color[self] := "white"
            }
         }
       }
  }
} *)
\* BEGIN TRANSLATION
VARIABLES network, active, color, counter

vars == << network, active, color, counter >>

ProcSet == Node

Init ==
  /\ network = [n \in Node |-> IF n = Initiator
                                 THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                                 ELSE EmptyBag]
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [n \in Node |-> 0]

SendMsg(self) ==
  /\ active[self]
  /\ \E to \in Node \ {self} :
        network' = [network EXCEPT ![to] = BagAdd(@, [type |-> "pl"])]
  /\ counter' = [counter EXCEPT ![self] = @ + 1]
  /\ UNCHANGED << active, color >>

RecvMsg(self) ==
  /\ \E msg \in DOMAIN network[self] :
        /\ msg.type = "pl"
        /\ counter' = [counter EXCEPT ![self] = @ - 1]
        /\ active' = [active EXCEPT ![self] = TRUE]
        /\ color' = [color EXCEPT ![self] = "black"]
        /\ network' = [network EXCEPT ![self] = BagRemove(@, msg)]

Deactivate(self) ==
  /\ active[self]
  /\ active' = [active EXCEPT ![self] = FALSE]
  /\ UNCHANGED << network, color, counter >>

PassToken(self) ==
  /\ self # Initiator
  /\ \E tok \in DOMAIN network[self] :
        /\ tok.type = "tok"
        /\ ~active[self]
        /\ network' = [network EXCEPT
              ![self-1] = BagAdd(@, [type |-> "tok", q |-> tok.q + counter[self],
                                     color |-> IF color[self] = "black"
                                                 THEN "black" ELSE tok.color]),
              ![self] = BagRemove(@, tok)]
        /\ color' = [color EXCEPT ![self] = "white"]
  /\ UNCHANGED << active, counter >>

InitiateToken(self) ==
  /\ self = Initiator
  /\ \E tok \in DOMAIN network[self] :
        /\ tok.type = "tok"
        /\ \/ color[self] = "black"
           \/ tok.q + counter[self] > 0
           \/ tok.color = "black"
        /\ network' = [network EXCEPT
              ![N-1] = BagAdd(@, [type |-> "tok", q |-> 0, color |-> "white"]),
              ![self] = BagRemove(@, tok)]
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
\* END TRANSLATION

-----------------------------------------------------------------------------

StateConstraint == \A i \in Node : counter[i] < 3

tokenPos == CHOOSE n \in Node : \E m \in DOMAIN network[n] : m.type = "tok"

tokenMsg == CHOOSE m \in DOMAIN network[tokenPos] : m.type = "tok"

token == [pos |-> tokenPos, q |-> tokenMsg.q, color |-> tokenMsg.color]

pending == [n \in Node |-> IF [type |-> "pl"] \in DOMAIN network[n]
                             THEN network[n][[type |-> "pl"]]
                             ELSE 0]

EWD998 == INSTANCE EWD998 WITH token <- token, pending <- pending

EWD998Spec == EWD998!Spec

Alias ==
  [ network |-> network,
    active  |-> active,
    color   |-> color,
    counter |-> counter,
    token   |-> token,
    pending |-> pending ]

=============================================================================