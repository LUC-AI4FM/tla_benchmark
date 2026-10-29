------------------------------- MODULE EWD998PCal -------------------------------
(***************************************************************************)
(* Safra's distributed termination detection algorithm (EWD 998) on a     *)
(* ring of N nodes. Messages (payloads and the token) are carried by a    *)
(* bag-based network: network[n] is the bag of messages pending at n.     *)
(***************************************************************************)
EXTENDS Integers, Naturals, Bags, FiniteSets, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node      == 0 .. N-1
Initiator == 0
Color     == {"white", "black"}

Payload   == [type |-> "pl"]
Token(q, c) == [type |-> "tok", q |-> q, color |-> c]

(***************************************************************************
--algorithm Safra {
  variables
    network = [ n \in Node |-> IF n = Initiator
                               THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                               ELSE EmptyBag ];

  fair process (node \in Node)
    variables active \in BOOLEAN, color = "black", counter = 0;
  {
    l: while (TRUE) {
      either {   \* send a payload message
        await active;
        with (to \in Node \ {self}) {
          network[to] := network[to] (+) SetToBag({[type |-> "pl"]});
        };
        counter := counter + 1;
      } or {     \* receive a payload message
        with (msg \in BagToSet(network[self])) {
          await msg.type = "pl";
          counter := counter - 1;
          active := TRUE;
          color := "black";
          network[self] := network[self] (-) SetToBag({msg});
        }
      } or {     \* become inactive
        active := FALSE;
      } or {     \* pass the token
        await self # Initiator /\ ~active;
        with (tok \in BagToSet(network[self])) {
          await tok.type = "tok";
          network[self] := network[self] (-) SetToBag({tok}) ||
          network[self-1] := network[self-1] (+)
              SetToBag({[type |-> "tok", q |-> tok.q + counter,
                         color |-> IF color = "black" THEN "black" ELSE tok.color]});
          color := "white";
        }
      } or {     \* initiator starts a new token round
        await self = Initiator;
        with (tok \in BagToSet(network[self])) {
          await tok.type = "tok" /\
                (tok.color = "black" \/ color = "black" \/ tok.q + counter # 0);
          network[self] := network[self] (-) SetToBag({tok}) ||
          network[N-1] := network[N-1] (+)
              SetToBag({[type |-> "tok", q |-> 0, color |-> "white"]});
          color := "white";
        }
      }
    }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES network, pc, active, color, counter

vars == << network, pc, active, color, counter >>

ProcSet == Node

Init == /\ network = [ n \in Node |-> IF n = Initiator
                                      THEN SetToBag({Token(0, "black")})
                                      ELSE EmptyBag ]
        /\ active \in [Node -> BOOLEAN]
        /\ color = [self \in Node |-> "black"]
        /\ counter = [self \in Node |-> 0]
        /\ pc = [self \in ProcSet |-> "l"]

SendMsg(self) ==
    /\ pc[self] = "l"
    /\ active[self]
    /\ \E to \in Node \ {self}:
          network' = [network EXCEPT ![to] = @ (+) SetToBag({Payload})]
    /\ counter' = [counter EXCEPT ![self] = @ + 1]
    /\ UNCHANGED << pc, active, color >>

RecvMsg(self) ==
    /\ pc[self] = "l"
    /\ \E msg \in BagToSet(network[self]):
          /\ msg.type = "pl"
          /\ counter' = [counter EXCEPT ![self] = @ - 1]
          /\ active' = [active EXCEPT ![self] = TRUE]
          /\ color' = [color EXCEPT ![self] = "black"]
          /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({msg})]
    /\ UNCHANGED pc

Deactivate(self) ==
    /\ pc[self] = "l"
    /\ active' = [active EXCEPT ![self] = FALSE]
    /\ UNCHANGED << network, pc, color, counter >>

PassToken(self) ==
    /\ pc[self] = "l"
    /\ self # Initiator
    /\ ~active[self]
    /\ \E tok \in BagToSet(network[self]):
          /\ tok.type = "tok"
          /\ network' = [network EXCEPT
                ![self]   = @ (-) SetToBag({tok}),
                ![self-1] = @ (+) SetToBag({Token(tok.q + counter[self],
                                 IF color[self] = "black" THEN "black" ELSE tok.color)})]
          /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << pc, active, counter >>

InitiateToken(self) ==
    /\ pc[self] = "l"
    /\ self = Initiator
    /\ \E tok \in BagToSet(network[self]):
          /\ tok.type = "tok"
          /\ \/ tok.color = "black"
             \/ color[self] = "black"
             \/ tok.q + counter[self] # 0
          /\ network' = [network EXCEPT
                ![self] = @ (-) SetToBag({tok}),
                ![N-1]  = @ (+) SetToBag({Token(0, "white")})]
          /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << pc, active, counter >>

l(self) == \/ SendMsg(self)
           \/ RecvMsg(self)
           \/ Deactivate(self)
           \/ PassToken(self)
           \/ InitiateToken(self)

node(self) == l(self)

Next == (\E self \in Node: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))
\* END TRANSLATION
-----------------------------------------------------------------------------

(***************************************************************************)
(* Auxiliary definitions, safety and liveness properties.                 *)
(***************************************************************************)
TokenMsgs(n) == { m \in BagToSet(network[n]) : m.type = "tok" }

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ pc \in [Node -> {"l"}]
    /\ \A n \in Node : IsABag(network[n])

\* Exactly one token circulates in the ring.
UniqueToken ==
    Cardinality({ n \in Node : TokenMsgs(n) # {} }) = 1

Termination ==
    /\ \A n \in Node : ~active[n]
    /\ \A n \in Node : CopiesIn(Payload, network[n]) = 0

terminationDetected ==
    /\ \E tok \in TokenMsgs(Initiator) :
          /\ tok.color = "white"
          /\ tok.q + counter[Initiator] = 0
    /\ color[Initiator] = "white"
    /\ ~active[Initiator]

Safety == terminationDetected => Termination

Liveness == Termination ~> terminationDetected

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the high-level EWD998 specification.             *)
(***************************************************************************)
pendingMap == [ n \in Node |-> CopiesIn(Payload, network[n]) ]

tokenMap ==
    LET pos == CHOOSE n \in Node : TokenMsgs(n) # {}
        tok == CHOOSE m \in TokenMsgs(pos) : TRUE
    IN [ pos |-> pos, q |-> tok.q, color |-> tok.color ]

EWD998 == INSTANCE EWD998 WITH active  <- active,
                               color   <- color,
                               counter <- counter,
                               pending <- pendingMap,
                               token   <- tokenMap

EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint bounding counters and pending messages for TLC.      *)
(***************************************************************************)
MaxCount == 3

StateConstraint ==
    \A n \in Node :
        /\ counter[n] <= MaxCount
        /\ counter[n] >= -MaxCount
        /\ CopiesIn(Payload, network[n]) <= MaxCount

=============================================================================