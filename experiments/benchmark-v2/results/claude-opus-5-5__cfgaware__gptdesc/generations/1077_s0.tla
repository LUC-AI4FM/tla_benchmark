------------------------------- MODULE EWD998PCal -------------------------------
EXTENDS Integers, Naturals, FiniteSets, Bags, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Initiator == 0

Color == {"white", "black"}

PL == [type |-> "pl"]

TokMsg(q, c) == [type |-> "tok", q |-> q, color |-> c]

(* --algorithm ewd998 {

variables
    network = [ n \in Node |-> IF n = Initiator
                                THEN SetToBag({TokMsg(0, "black")})
                                ELSE EmptyBag ];

fair process (n \in Node)
    variables active \in BOOLEAN, color = "black", counter = 0;
{
l:  while (TRUE) {
        either {     \* send a payload message to some other node
            await active;
            with (to \in Node \ {self}) {
                network[to] := network[to] (+) SetToBag({PL});
            };
            counter := counter + 1;
        } or {       \* receive a payload message
            await CopiesIn(PL, network[self]) > 0;
            network[self] := network[self] (-) SetToBag({PL});
            counter := counter - 1;
            active := TRUE;
            color := "black";
        } or {       \* become inactive
            await active;
            active := FALSE;
        } or {       \* pass the token
            await self # Initiator /\ ~active;
            with (tok \in {m \in BagToSet(network[self]) : m.type = "tok"}) {
                network[self] := network[self] (-) SetToBag({tok}) ||
                network[self-1] := network[self-1] (+)
                     SetToBag({TokMsg(tok.q + counter,
                                      IF color = "black" THEN "black" ELSE tok.color)});
            };
            color := "white";
        } or {       \* initiator restarts the token round
            await self = Initiator;
            with (tok \in {m \in BagToSet(network[self]) : m.type = "tok"}) {
                await tok.color = "black" \/ color = "black" \/ tok.q + counter # 0;
                network[self] := network[self] (-) SetToBag({tok}) ||
                network[N-1] := network[N-1] (+) SetToBag({TokMsg(0, "white")});
            };
            color := "white";
        }
    }
}
} *)
\* BEGIN TRANSLATION
VARIABLES network, active, color, counter

vars == << network, active, color, counter >>

ProcSet == Node

Init == (* Global variables *)
        /\ network = [ n \in Node |-> IF n = Initiator
                                      THEN SetToBag({TokMsg(0, "black")})
                                      ELSE EmptyBag ]
        (* Process n *)
        /\ active \in [Node -> BOOLEAN]
        /\ color = [self \in Node |-> "black"]
        /\ counter = [self \in Node |-> 0]

SendMsg(self) ==
    /\ active[self]
    /\ \E to \in Node \ {self}:
          network' = [network EXCEPT ![to] = @ (+) SetToBag({PL})]
    /\ counter' = [counter EXCEPT ![self] = @ + 1]
    /\ UNCHANGED << active, color >>

RecvMsg(self) ==
    /\ CopiesIn(PL, network[self]) > 0
    /\ network' = [network EXCEPT ![self] = @ (-) SetToBag({PL})]
    /\ counter' = [counter EXCEPT ![self] = @ - 1]
    /\ active' = [active EXCEPT ![self] = TRUE]
    /\ color' = [color EXCEPT ![self] = "black"]

Deactivate(self) ==
    /\ active[self]
    /\ active' = [active EXCEPT ![self] = FALSE]
    /\ UNCHANGED << network, color, counter >>

PassToken(self) ==
    /\ self # Initiator
    /\ ~ active[self]
    /\ \E tok \in {m \in BagToSet(network[self]) : m.type = "tok"}:
          network' = [network EXCEPT
                        ![self]   = @ (-) SetToBag({tok}),
                        ![self-1] = @ (+) SetToBag({TokMsg(tok.q + counter[self],
                                         IF color[self] = "black" THEN "black" ELSE tok.color)})]
    /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << active, counter >>

InitiateToken(self) ==
    /\ self = Initiator
    /\ \E tok \in {m \in BagToSet(network[self]) : m.type = "tok"}:
          /\ tok.color = "black" \/ color[self] = "black" \/ tok.q + counter[self] # 0
          /\ network' = [network EXCEPT
                           ![self] = @ (-) SetToBag({tok}),
                           ![N-1]  = @ (+) SetToBag({TokMsg(0, "white")})]
    /\ color' = [color EXCEPT ![self] = "white"]
    /\ UNCHANGED << active, counter >>

n(self) == \/ SendMsg(self)
           \/ RecvMsg(self)
           \/ Deactivate(self)
           \/ PassToken(self)
           \/ InitiateToken(self)

Next == (\E self \in Node: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(n(self))

\* END TRANSLATION
-----------------------------------------------------------------------------

\* Refinement mapping to EWD998.
TokenPos == CHOOSE i \in Node : \E m \in BagToSet(network[i]) : m.type = "tok"

TheToken == CHOOSE m \in BagToSet(network[TokenPos]) : m.type = "tok"

token == [ pos   |-> TokenPos,
           q     |-> TheToken.q,
           color |-> TheToken.color ]

pending == [ i \in Node |-> CopiesIn(PL, network[i]) ]

EWD998 == INSTANCE EWD998 WITH active <- active,
                               color <- color,
                               counter <- counter,
                               pending <- pending,
                               token <- token

EWD998Spec == EWD998!Spec

-----------------------------------------------------------------------------

StateConstraint ==
    /\ \A i \in Node :
          /\ counter[i] \in -3 .. 3
          /\ CopiesIn(PL, network[i]) <= 3
    /\ TheToken.q \in -3 .. 3

Alias ==
    [ network |-> network,
      active  |-> active,
      color   |-> color,
      counter |-> counter,
      pending |-> pending,
      token   |-> token ]

=============================================================================