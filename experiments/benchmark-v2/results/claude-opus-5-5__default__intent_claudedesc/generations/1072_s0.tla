------------------------------ MODULE EWD998ChanID ------------------------------
(***************************************************************************)
(* EWD998 termination detection on a ring of named nodes, communicating    *)
(* over FIFO-free channels (inboxes), with vector clocks.                  *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANT Nodes

ASSUME NodesAssumption == IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

Initiator == CHOOSE n \in Nodes : TRUE

RECURSIVE Iter(_, _, _)
Iter(f, k, x) == IF k = 0 THEN x ELSE Iter(f, k - 1, f[x])

\* r is a simple directed cycle through all nodes.
IsSimpleCycle(S, r) ==
    \A n \in S : \E k \in 1..Cardinality(S) : Iter(r, k, Initiator) = n

RingOfNodes == CHOOSE r \in [Nodes -> Nodes] : IsSimpleCycle(Nodes, r)

ASSUME RingAssumption == \E r \in [Nodes -> Nodes] : IsSimpleCycle(Nodes, r)

Color == {"white", "black"}

Max(a, b) == IF a > b THEN a ELSE b

\* Vector clock helpers
VC == [Nodes -> Nat]
Tick(n, vc) == [vc EXCEPT ![n] = @ + 1]
Merge(a, b) == [m \in Nodes |-> Max(a[m], b[m])]

RemoveAt(s, j) == SubSeq(s, 1, j - 1) \o SubSeq(s, j + 1, Len(s))

VARIABLES active, color, counter, inbox, clock, rounds

vars == <<active, color, counter, inbox, clock, rounds>>

TokenMsg == [type : {"tok"}, q : Int, color : Color, vc : VC]
PayloadMsg == [type : {"pl"}, src : Nodes, vc : VC]
Message == TokenMsg \cup PayloadMsg

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter \in [Nodes -> Int]
    /\ inbox \in [Nodes -> Seq(Message)]
    /\ clock \in [Nodes -> VC]
    /\ rounds \in Nat
    \* Exactly one token in the system.
    /\ Cardinality({ <<n, j>> \in Nodes \X Nat :
                        /\ j \in 1..Len(inbox[n])
                        /\ inbox[n][j].type = "tok" }) = 1

-----------------------------------------------------------------------------
(* Termination and its detection *)

Termination ==
    /\ \A n \in Nodes : ~ active[n]
    /\ \A n \in Nodes : \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

TerminationDetected ==
    /\ \E j \in 1..Len(inbox[Initiator]) :
          /\ inbox[Initiator][j].type = "tok"
          /\ inbox[Initiator][j].color = "white"
          /\ inbox[Initiator][j].q + counter[Initiator] = 0
    /\ color[Initiator] = "white"
    /\ ~ active[Initiator]

-----------------------------------------------------------------------------
Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter = [n \in Nodes |-> 0]
    /\ clock = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ inbox = [n \in Nodes |->
                  IF n = Initiator
                  THEN << [type |-> "tok", q |-> 0, color |-> "black",
                           vc |-> [m \in Nodes |-> 0]] >>
                  ELSE << >>]
    /\ rounds = IF Termination THEN 1 ELSE 0

(* History variable: number of token rounds since actual termination.    *)
(* The round in progress at termination is round 1; every probe started *)
(* afterwards opens a new round.                                         *)
UpdRounds(probe) ==
    rounds' = IF ~ Termination' THEN 0
              ELSE IF ~ Termination THEN 1
              ELSE IF probe THEN rounds + 1
              ELSE rounds

InitiateProbe ==
    /\ ~ active[Initiator]
    /\ \E j \in 1..Len(inbox[Initiator]) :
          LET tok == inbox[Initiator][j]
              vc  == Tick(Initiator, Merge(clock[Initiator], tok.vc))
          IN
          /\ tok.type = "tok"
          /\ \/ tok.color = "black"
             \/ color[Initiator] = "black"
             \/ counter[Initiator] + tok.q # 0
          /\ clock' = [clock EXCEPT ![Initiator] = vc]
          /\ inbox' =
               IF RingOfNodes[Initiator] = Initiator
               THEN [inbox EXCEPT ![Initiator] =
                       Append(RemoveAt(@, j),
                              [type |-> "tok", q |-> 0,
                               color |-> "white", vc |-> vc])]
               ELSE [inbox EXCEPT
                       ![RingOfNodes[Initiator]] =
                          Append(@, [type |-> "tok", q |-> 0,
                                     color |-> "white", vc |-> vc]),
                       ![Initiator] = RemoveAt(@, j)]
    /\ color' = [color EXCEPT ![Initiator] = "white"]
    /\ UNCHANGED <<active, counter>>

PassToken(n) ==
    /\ n # Initiator
    /\ ~ active[n]
    /\ \E j \in 1..Len(inbox[n]) :
          LET tok == inbox[n][j]
              vc  == Tick(n, Merge(clock[n], tok.vc))
          IN
          /\ tok.type = "tok"
          /\ clock' = [clock EXCEPT ![n] = vc]
          /\ inbox' = [inbox EXCEPT
                         ![RingOfNodes[n]] =
                            Append(@, [type  |-> "tok",
                                       q     |-> tok.q + counter[n],
                                       color |-> IF color[n] = "black"
                                                 THEN "black"
                                                 ELSE tok.color,
                                       vc    |-> vc]),
                         ![n] = RemoveAt(@, j)]
    /\ color' = [color EXCEPT ![n] = "white"]
    /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E n \in Nodes \ {Initiator} : PassToken(n)

SendMsg(n) ==
    /\ active[n]
    /\ \E m \in Nodes \ {n} :
          LET vc == Tick(n, clock[n]) IN
          /\ clock' = [clock EXCEPT ![n] = vc]
          /\ inbox' = [inbox EXCEPT
                         ![m] = Append(@, [type |-> "pl", src |-> n, vc |-> vc])]
    /\ counter' = [counter EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<active, color>>

RecvMsg(n) ==
    /\ \E j \in 1..Len(inbox[n]) :
          /\ inbox[n][j].type = "pl"
          /\ clock' = [clock EXCEPT ![n] = Tick(n, Merge(clock[n], inbox[n][j].vc))]
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
    /\ counter' = [counter EXCEPT ![n] = @ - 1]
    /\ color' = [color EXCEPT ![n] = "black"]
    /\ active' = [active EXCEPT ![n] = TRUE]

Deactivate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ clock' = [clock EXCEPT ![n] = Tick(n, @)]
    /\ UNCHANGED <<color, counter, inbox>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

Next ==
    \/ InitiateProbe /\ UpdRounds(TRUE)
    \/ (\E n \in Nodes \ {Initiator} : PassToken(n)) /\ UpdRounds(FALSE)
    \/ Environment /\ UpdRounds(FALSE)

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Correctness properties *)

Safety == TerminationDetected => Termination

Inv == Safety

TerminationStable == [](Termination => []Termination)

Liveness == Termination ~> TerminationDetected

\* Termination is detected within at most three token rounds after it occurs.
AtMostThreeRounds == rounds <= 3

BoundedDetection == [](Termination => <>(TerminationDetected /\ rounds <= 3))

THEOREM Spec => [](TypeOK /\ Safety /\ AtMostThreeRounds)
THEOREM Spec => Liveness

-----------------------------------------------------------------------------
(* Refinement mapping to the natural-number-indexed EWD998Chan spec.      *)
(* Node at ring distance k from the Initiator (in token direction) gets  *)
(* index N - k (mod N): Initiator is 0, and the token travels i -> i-1.   *)

Nat2Node(i) == IF i = 0 THEN Initiator ELSE Iter(RingOfNodes, N - i, Initiator)

Node2Nat(n) == CHOOSE i \in 0..(N - 1) : Nat2Node(i) = n

StripMsg(msg) ==
    IF msg.type = "tok"
    THEN [type |-> "tok", q |-> msg.q, color |-> msg.color]
    ELSE [type |-> "pl"]

StripSeq(s) == [k \in 1..Len(s) |-> StripMsg(s[k])]

activeBar  == [i \in 0..(N - 1) |-> active[Nat2Node(i)]]
colorBar   == [i \in 0..(N - 1) |-> color[Nat2Node(i)]]
counterBar == [i \in 0..(N - 1) |-> counter[Nat2Node(i)]]
inboxBar   == [i \in 0..(N - 1) |-> StripSeq(inbox[Nat2Node(i)])]

(***************************************************************************)
(* With EWD998Chan.tla on the module path, the refinement is stated as:   *)
(*                                                                         *)
(*   EWD998Chan == INSTANCE EWD998Chan WITH N <- N,                        *)
(*                   active <- activeBar, color <- colorBar,               *)
(*                   counter <- counterBar, inbox <- inboxBar              *)
(*   EWD998ChanSpec == EWD998Chan!Spec                                     *)
(*   THEOREM Spec => EWD998ChanSpec                                        *)
(***************************************************************************)

=============================================================================