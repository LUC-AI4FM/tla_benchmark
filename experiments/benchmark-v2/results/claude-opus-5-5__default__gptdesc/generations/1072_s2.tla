--------------------------- MODULE EWD998ChanID ---------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Nodes

ASSUME NodesAssumption == IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

\* The initiator can be any node, as long as it is always the same one.
Initiator == CHOOSE n \in Nodes : TRUE

\* Follow the successor function r for k steps, starting at the initiator.
RECURSIVE IterR(_, _)
IterR(r, k) == IF k = 0 THEN Initiator ELSE r[IterR(r, k - 1)]

\* r is a ring if it visits every node within N steps from the initiator.
IsRing(r) == { IterR(r, k) : k \in 1..N } = Nodes

\* Arrange the nodes in a ring. RingOfNodes[n] is the node that n passes the token to.
RingOfNodes == CHOOSE r \in [Nodes -> Nodes] : IsRing(r)

Color == {"white", "black"}

VARIABLES
  active,   \* activation status of each node
  color,    \* color of each node
  counter,  \* local message counter (sent minus received)
  inbox,    \* message channel of each node
  clock,    \* vector clock of each node
  passes    \* auxiliary: number of token passes since global termination

vars == <<active, color, counter, inbox, clock, passes>>

----------------------------------------------------------------------------
(* Vector clocks *)

ZeroClock == [m \in Nodes |-> 0]

Merge(a, b) == [m \in Nodes |-> IF a[m] > b[m] THEN a[m] ELSE b[m]]

Tick(n, vc) == [vc EXCEPT ![n] = @ + 1]

(* Remove the element at index i from sequence s. *)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

----------------------------------------------------------------------------

TokenMsg ==
  [type : {"tok"}, q : Int, color : Color, vc : [Nodes -> Nat]]

PayloadMsg ==
  [type : {"pl"}, vc : [Nodes -> Nat]]

Message == TokenMsg \cup PayloadMsg

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter \in [Nodes -> Int]
  /\ inbox \in [Nodes -> Seq(Message)]
  /\ clock \in [Nodes -> [Nodes -> Nat]]
  /\ passes \in Nat
  \* Exactly one token is in transit.
  /\ Cardinality({ <<n, j>> \in { <<m, i>> : m \in Nodes, i \in 1..Len(inbox[m]) } :
                      inbox[n][j].type = "tok" }) = 1

----------------------------------------------------------------------------

Termination ==
  /\ \A n \in Nodes : ~ active[n]
  /\ \A n \in Nodes : \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

TerminationDetected ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
       /\ inbox[Initiator][j].type = "tok"
       /\ inbox[Initiator][j].color = "white"
       /\ counter[Initiator] + inbox[Initiator][j].q = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

----------------------------------------------------------------------------

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter = [n \in Nodes |-> 0]
  /\ inbox = [n \in Nodes |->
                IF n = Initiator
                THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> ZeroClock] >>
                ELSE << >>]
  /\ clock = [n \in Nodes |-> ZeroClock]
  /\ passes = 0

\* Count token passes once the system has terminated; reset otherwise.
NextPasses == passes' = IF Termination THEN passes + 1 ELSE 0

InitiateProbe ==
  /\ ~ active[Initiator]
  /\ \E j \in 1..Len(inbox[Initiator]) :
       LET tkn == inbox[Initiator][j]
           newClock == Tick(Initiator, Merge(clock[Initiator], tkn.vc))
       IN
       /\ tkn.type = "tok"
       \* Previous round inconclusive.
       /\ \/ tkn.color = "black"
          \/ color[Initiator] = "black"
          \/ counter[Initiator] + tkn.q # 0
       /\ inbox' = [inbox EXCEPT
                      ![Initiator] = RemoveAt(@, j),
                      ![RingOfNodes[Initiator]] =
                          Append(@, [type |-> "tok", q |-> 0,
                                     color |-> "white", vc |-> newClock])]
       /\ clock' = [clock EXCEPT ![Initiator] = newClock]
  /\ color' = [color EXCEPT ![Initiator] = "white"]
  /\ NextPasses
  /\ UNCHANGED <<active, counter>>

PassToken(n) ==
  /\ n # Initiator
  /\ ~ active[n]
  /\ \E j \in 1..Len(inbox[n]) :
       LET tkn == inbox[n][j]
           newClock == Tick(n, Merge(clock[n], tkn.vc))
       IN
       /\ tkn.type = "tok"
       /\ inbox' = [inbox EXCEPT
                      ![n] = RemoveAt(@, j),
                      ![RingOfNodes[n]] =
                          Append(@, [type |-> "tok",
                                     q |-> tkn.q + counter[n],
                                     color |-> IF color[n] = "black"
                                               THEN "black" ELSE tkn.color,
                                     vc |-> newClock])]
       /\ clock' = [clock EXCEPT ![n] = newClock]
  /\ color' = [color EXCEPT ![n] = "white"]
  /\ NextPasses
  /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E n \in Nodes \ {Initiator} : PassToken(n)

----------------------------------------------------------------------------

SendMsg(n) ==
  /\ active[n]
  /\ \E rcv \in Nodes \ {n} :
       LET newClock == Tick(n, clock[n]) IN
       /\ inbox' = [inbox EXCEPT ![rcv] = Append(@, [type |-> "pl", vc |-> newClock])]
       /\ clock' = [clock EXCEPT ![n] = newClock]
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ passes' = 0
  /\ UNCHANGED <<active, color>>

RecvMsg(n) ==
  /\ \E j \in 1..Len(inbox[n]) :
       LET msg == inbox[n][j]
           newClock == Tick(n, Merge(clock[n], msg.vc))
       IN
       /\ msg.type = "pl"
       /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
       /\ clock' = [clock EXCEPT ![n] = newClock]
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ color' = [color EXCEPT ![n] = "black"]
  /\ passes' = 0

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ clock' = [clock EXCEPT ![n] = Tick(n, @)]
  /\ passes' = 0
  /\ UNCHANGED <<color, counter, inbox>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

----------------------------------------------------------------------------
(* Properties *)

Safety == TerminationDetected => Termination

Liveness == Termination ~> TerminationDetected

\* Termination is detected within at most three token rounds after
\* the system terminated (each round consists of N token passes).
BoundedRounds == passes <= 3 * N

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => []BoundedRounds

----------------------------------------------------------------------------
(* Refinement mapping to EWD998Chan, whose nodes are 0..N-1, whose          *)
(* initiator is 0, and where node i passes the token to node i-1.           *)

Walk(k) == IterR(RingOfNodes, k)

\* Natural number i corresponds to the node reached from the initiator
\* after (N - i) % N token passes.
Nat2Node(i) == Walk((N - i) % N)

MapMsg(m) ==
  IF m.type = "tok"
  THEN [type |-> "tok", q |-> m.q, color |-> m.color]
  ELSE [type |-> "pl"]

MapSeq(s) == [i \in 1..Len(s) |-> MapMsg(s[i])]

EWD998Chan == INSTANCE EWD998Chan WITH
  N <- N,
  active <- [i \in 0..N-1 |-> active[Nat2Node(i)]],
  color <- [i \in 0..N-1 |-> color[Nat2Node(i)]],
  counter <- [i \in 0..N-1 |-> counter[Nat2Node(i)]],
  inbox <- [i \in 0..N-1 |-> MapSeq(inbox[Nat2Node(i)])]

EWD998ChanSafety == EWD998Chan!Init /\ [][EWD998Chan!Next]_(EWD998Chan!vars)

THEOREM SafetyRefinement == Spec => EWD998ChanSafety

THEOREM LivenessRefinement == Spec => EWD998Chan!Spec

=============================================================================