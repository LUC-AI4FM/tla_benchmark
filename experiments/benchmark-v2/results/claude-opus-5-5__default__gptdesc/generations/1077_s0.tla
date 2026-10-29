---------------------------- MODULE EWD998PCal ----------------------------
(***************************************************************************)
(* Safra's distributed termination detection algorithm (EWD 998) on a     *)
(* ring of N nodes. The network is a bag of messages per node: payload    *)
(* messages and a single circulating token carrying fields q and color.   *)
(***************************************************************************)
EXTENDS Integers, Naturals, Bags, FiniteSets, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Initiator == 0

Color == {"white", "black"}

(* --algorithm ewd998 {
  variables
    network = [n \in Node |-> IF n = Initiator
                               THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                               ELSE EmptyBag];

  fair process (node \in Node)
    variables active \in BOOLEAN, color \in Color, counter = 0;
  {
    l: while (TRUE) {
         either { \* send some payload message to some other node.
            when active;
            with (to \in Node \ {self}) {
               network[to] := network[to] (+) SetToBag({[type |-> "pl"]});
            };
            counter := counter + 1
         } or { \* receive a payload message. Reactivates the node.
            with (msg \in DOMAIN network[self]) {
               when msg.type = "pl";
               counter := counter - 1;
               active := TRUE;
               color := "black";
               network[self] := network[self] (-) SetToBag({msg})
            }
         } or { \* terminate the current node.
            active := FALSE
         } or { \* pass the token to the next node.
            when self # Initiator;
            with (tok \in DOMAIN network[self]) {
               when tok.type = "tok" /\ ~active;
               network[self] := network[self] (-) SetToBag({tok}) ||
               network[self-1] := network[self-1] (+)
                   SetToBag({[type |-> "tok", q |-> tok.q + counter,
                              color |-> (IF color = "black" THEN "black" ELSE tok.color)]});
               color := "white";
            }
         } or { \* initiate (restart) the token.
            when self = Initiator;
            with (tok \in DOMAIN network[self]) {
               when tok.type = "tok" /\ (color = "black" \/ tok.q + counter # 0 \/ tok.color = "black");
               network[self] := network[self] (-) SetToBag({tok}) ||
               network[N-1] := network[N-1] (+)
                   SetToBag({[type |-> "tok", q |-> 0, color |-> "white"]});
               color := "white";
            }
         }
       }
  }
}
*)

\* BEGIN TRANSLATION
VARIABLES network, pc, active, color, counter

vars == << network, pc, active, color, counter >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ network = [n \in Node |-> IF n = Initiator
                                      THEN SetToBag({[type |-> "tok", q |-> 0, color |-> "black"]})
                                      ELSE EmptyBag]
        (* Process node *)
        /\ active \in [Node -> BOOLEAN]
        /\ color \in [Node -> Color]
        /\ counter = [self \in Node |-> 0]
        /\ pc = [self \in ProcSet |-> "l"]

l(self) == /\ pc[self] = "l"
           /\ \/ /\ active[self]
                 /\ \E to \in Node \ {self}:
                      network' = [network EXCEPT ![to] = network[to] (+) SetToBag({[type |-> "pl"]})]
                 /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                 /\ UNCHANGED << active, color >>
              \/ /\ \E msg \in DOMAIN network[self]:
                      /\ msg.type = "pl"
                      /\ counter' = [counter EXCEPT ![self] = counter[self] - 1]
                      /\ active' = [active EXCEPT ![self] = TRUE]
                      /\ color' = [color EXCEPT ![self] = "black"]
                      /\ network' = [network EXCEPT ![self] = network[self] (-) SetToBag({msg})]
              \/ /\ active' = [active EXCEPT ![self] = FALSE]
                 /\ UNCHANGED << network, color, counter >>
              \/ /\ self # Initiator
                 /\ \E tok \in DOMAIN network[self]:
                      /\ tok.type = "tok" /\ ~active[self]
                      /\ network' = [network EXCEPT
                                       ![self] = network[self] (-) SetToBag({tok}),
                                       ![self-1] = network[self-1] (+)
                                          SetToBag({[type |-> "tok", q |-> tok.q + counter[self],
                                                     color |-> (IF color[self] = "black"
                                                                THEN "black" ELSE tok.color)]})]
                      /\ color' = [color EXCEPT ![self] = "white"]
                 /\ UNCHANGED << active, counter >>
              \/ /\ self = Initiator
                 /\ \E tok \in DOMAIN network[self]:
                      /\ tok.type = "tok"
                      /\ (color[self] = "black" \/ tok.q + counter[self] # 0 \/ tok.color = "black")
                      /\ network' = [network EXCEPT
                                       ![self] = network[self] (-) SetToBag({tok}),
                                       ![N-1] = network[N-1] (+)
                                          SetToBag({[type |-> "tok", q |-> 0, color |-> "white"]})]
                      /\ color' = [color EXCEPT ![self] = "white"]
                 /\ UNCHANGED << active, counter >>
           /\ pc' = [pc EXCEPT ![self] = "l"]

node(self) == l(self)

Next == (\E self \in Node: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement-style comparison with the high-level EWD998 specification.  *)
(***************************************************************************)

tokenMap ==
    LET pos == CHOOSE i \in Node : \E m \in DOMAIN network[i] : m.type = "tok"
        tok == CHOOSE m \in DOMAIN network[pos] : m.type = "tok"
    IN [pos |-> pos, q |-> tok.q, color |-> tok.color]

pendingMap ==
    [n \in Node |-> IF [type |-> "pl"] \in DOMAIN network[n]
                    THEN network[n][[type |-> "pl"]]
                    ELSE 0]

EWD998 == INSTANCE EWD998 WITH token <- tokenMap, pending <- pendingMap

EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* State constraint bounding counters and message counts for TLC.         *)
(***************************************************************************)

StateConstraint ==
    /\ \A i \in Node : counter[i] < 3
    /\ \A i \in Node : pendingMap[i] < 3
    /\ tokenMap.q < 9

=============================================================================