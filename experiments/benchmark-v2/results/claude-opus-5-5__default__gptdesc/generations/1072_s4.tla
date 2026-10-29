------------------------------- MODULE EWD998ChanID -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Nodes
ASSUME IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

\* A distinguished initiator.
Initiator == CHOOSE n \in Nodes : TRUE

\* A bijection from 0..N-1 onto Nodes with the initiator at position 0.
Nat2Node ==
  CHOOSE f \in [0..(N-1) -> Nodes] :
     /\ f[0] = Initiator
     /\ \A n \in Nodes : \E i \in 0..(N-1) : f[i] = n

Node2Nat == [n \in Nodes |-> CHOOSE i \in 0..(N-1) : Nat2Node[i] = n]

\* Organize the nodes in a ring. The token travels from node n to RingOfNodes[n].
RingOfNodes == [n \in Nodes |-> Nat2Node[(Node2Nat[n] - 1 + N) % N]]

Color == {"white", "black"}

Max(a, b) == IF a > b THEN a ELSE b

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

VARIABLES
  active,   \* activation status of nodes
  color,    \* color of nodes
  counter,  \* nb of sent messages - nb of received messages per node
  inbox,    \* channels of nodes
  clock,    \* vector clock of each node
  rounds    \* auxiliary: number of probes initiated after termination

vars == <<active, color, counter, inbox, clock, rounds>>

VC == [Nodes -> Nat]

TokenMsg == [type : {"tok"}, q : Int, color : Color, vc : VC]
BasicMsg == [type : {"pl"}, src : Nodes, vc : VC]
Message  == TokenMsg \cup BasicMsg

ZeroVC == [m \in Nodes |-> 0]

\* Tick the clock of node n and merge it with the clock v carried by a message.
Merge(n, mine, v) ==
  [m \in Nodes |-> IF m = n THEN mine[m] + 1 ELSE Max(mine[m], v[m])]

Tick(n, mine) == [mine EXCEPT ![n] = @ + 1]

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter \in [Nodes -> Int]
  /\ inbox \in [Nodes -> Seq(Message)]
  /\ clock \in [Nodes -> VC]
  /\ rounds \in Nat
  \* exactly one token in the system
  /\ Cardinality({ <<n, j>> \in Nodes \X (1..10000) :
                     j \in 1..Len(inbox[n]) /\ inbox[n][j].type = "tok" }) = 1

------------------------------------------------------------------------------

Termination ==
  /\ \A n \in Nodes : ~ active[n]
  /\ \A n \in Nodes : \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

terminationDetected ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
        /\ inbox[Initiator][j].type = "tok"
        /\ inbox[Initiator][j].color = "white"
        /\ inbox[Initiator][j].q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

------------------------------------------------------------------------------

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter = [n \in Nodes |-> 0]
  /\ clock = [n \in Nodes |-> ZeroVC]
  /\ inbox = [n \in Nodes |->
                IF n = Initiator
                THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> ZeroVC] >>
                ELSE << >>]
  /\ rounds = 0

InitiateProbe ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
       LET tok == inbox[Initiator][j] IN
       /\ tok.type = "tok"
       /\ \/ tok.color = "black"
          \/ color[Initiator] = "black"
          \/ counter[Initiator] + tok.q > 0
       /\ clock' = [clock EXCEPT ![Initiator] = Merge(Initiator, @, tok.vc)]
       /\ inbox' = [inbox EXCEPT
                      ![RingOfNodes[Initiator]] =
                          Append(@, [type |-> "tok", q |-> 0, color |-> "white",
                                     vc |-> clock'[Initiator]]),
                      ![Initiator] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![Initiator] = "white"]
  /\ rounds' = IF Termination THEN rounds + 1 ELSE 0
  /\ UNCHANGED <<active, counter>>

PassToken(n) ==
  /\ n # Initiator
  /\ ~ active[n]
  /\ \E j \in 1..Len(inbox[n]) :
       LET tok == inbox[n][j] IN
       /\ tok.type = "tok"
       /\ clock' = [clock EXCEPT ![n] = Merge(n, @, tok.vc)]
       /\ inbox' = [inbox EXCEPT
                      ![RingOfNodes[n]] =
                          Append(@, [type |-> "tok",
                                     q |-> tok.q + counter[n],
                                     color |-> IF color[n] = "black"
                                               THEN "black" ELSE tok.color,
                                     vc |-> clock'[n]]),
                      ![n] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![n] = "white"]
  /\ UNCHANGED <<active, counter, rounds>>

System == InitiateProbe \/ \E n \in Nodes : PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  /\ active[n]
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ clock' = [clock EXCEPT ![n] = Tick(n, @)]
  /\ \E j \in Nodes \ {n} :
       inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl", src |-> n,
                                                vc |-> clock'[n]])]
  /\ UNCHANGED <<active, color, rounds>>

RecvMsg(n) ==
  /\ \E j \in 1..Len(inbox[n]) :
       /\ inbox[n][j].type = "pl"
       /\ clock' = [clock EXCEPT ![n] = Merge(n, @, inbox[n][j].vc)]
       /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ color' = [color EXCEPT ![n] = "black"]
  /\ UNCHANGED rounds

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ clock' = [clock EXCEPT ![n] = Tick(n, @)]
  /\ UNCHANGED <<color, inbox, counter, rounds>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

\* Safety: termination is only detected when the system has terminated.
TerminationDetection == terminationDetected => Termination

\* Liveness: termination is eventually detected.
Liveness == Termination ~> terminationDetected

\* Bounded rounds: after termination, detection happens within at most
\* three token rounds initiated by the initiator.
BoundedRounds == rounds <= 3

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => []BoundedRounds
THEOREM Spec => Liveness

-----------------------------------------------------------------------------

\* Refinement mapping to EWD998Chan (nodes 0..N-1, initiator 0, token from i to i-1).

StripMsg(m) ==
  IF m.type = "pl"
  THEN [type |-> "pl"]
  ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

EWD998ChanInst ==
  INSTANCE EWD998Chan WITH
    N       <- N,
    active  <- [i \in 0..(N-1) |-> active[Nat2Node[i]]],
    color   <- [i \in 0..(N-1) |-> color[Nat2Node[i]]],
    counter <- [i \in 0..(N-1) |-> counter[Nat2Node[i]]],
    inbox   <- [i \in 0..(N-1) |->
                  [j \in 1..Len(inbox[Nat2Node[i]]) |->
                      StripMsg(inbox[Nat2Node[i]][j])]]

EWD998ChanSafety == EWD998ChanInst!Init /\ [][EWD998ChanInst!Next]_(EWD998ChanInst!vars)

EWD998ChanSpec == EWD998ChanInst!Spec

THEOREM Spec => EWD998ChanSafety
THEOREM Spec => EWD998ChanSpec

=============================================================================