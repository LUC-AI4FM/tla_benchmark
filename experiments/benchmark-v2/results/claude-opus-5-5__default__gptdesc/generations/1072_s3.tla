---------------------------- MODULE EWD998ChanID ----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes

ASSUME NodesAssumption == IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

\* A distinguished node acting as the initiator of the token.
Initiator == CHOOSE n \in Nodes : TRUE

-----------------------------------------------------------------------------
\* Helpers

Max(a, b) == IF a >= b THEN a ELSE b

RemoveAt(s, i) == [k \in 1..(Len(s) - 1) |-> IF k < i THEN s[k] ELSE s[k + 1]]

RECURSIVE Iterate(_, _, _)
Iterate(r, n, k) == IF k = 0 THEN n ELSE r[Iterate(r, n, k - 1)]

\* r forms a single cycle through all nodes.
IsSimpleCycle(r) == \A n \in Nodes : \E k \in 1..N : Iterate(r, Initiator, k) = n

\* Organize Nodes in a ring: the token is passed from n to RingOfNodes[n].
RingOfNodes == CHOOSE r \in [Nodes -> Nodes] : IsSimpleCycle(r)

\* Node reached after k token passes starting at the initiator.
NodeAt(k) == Iterate(RingOfNodes, Initiator, k)

\* Distance of node n from the initiator along the ring.
Dist(n) == CHOOSE k \in 0..(N - 1) : NodeAt(k) = n

-----------------------------------------------------------------------------

Color == {"white", "black"}

VARIABLES
    active,    \* activation status of nodes
    color,     \* color of nodes
    counter,   \* number of sent minus received messages per node
    inbox,     \* channels (sequences of messages) per node
    clock,     \* vector clock per node
    passes     \* number of token passes since global termination

vars == <<active, color, counter, inbox, clock, passes>>

VC == [Nodes -> Nat]

ZeroVC == [m \in Nodes |-> 0]

PlMsg == [type : {"pl"}, src : Nodes, vc : VC]
TokMsg == [type : {"tok"}, q : Int, color : Color, vc : VC]
Message == PlMsg \cup TokMsg

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter \in [Nodes -> Int]
    /\ inbox \in [Nodes -> Seq(Message)]
    /\ clock \in [Nodes -> VC]
    /\ passes \in Nat
    \* Exactly one token in the system.
    /\ \E n \in Nodes :
          /\ \E j \in 1..Len(inbox[n]) : inbox[n][j].type = "tok"
          /\ \A j, k \in 1..Len(inbox[n]) :
                (inbox[n][j].type = "tok" /\ inbox[n][k].type = "tok") => j = k
          /\ \A m \in Nodes \ {n} :
                \A j \in 1..Len(inbox[m]) : inbox[m][j].type # "tok"

-----------------------------------------------------------------------------

Tick(n) == [clock EXCEPT ![n] = [@ EXCEPT ![n] = @ + 1]]

Merge(n, vc) ==
    [clock EXCEPT ![n] =
        [m \in Nodes |-> IF m = n THEN Max(clock[n][m], vc[m]) + 1
                                  ELSE Max(clock[n][m], vc[m])]]

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

PassesUpd == passes' = IF Termination THEN passes + 1 ELSE passes

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter = [n \in Nodes |-> 0]
    /\ inbox = [n \in Nodes |->
                  IF n = Initiator
                  THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> ZeroVC] >>
                  ELSE << >>]
    /\ clock = [n \in Nodes |-> ZeroVC]
    /\ passes = 0

InitiateProbe ==
    /\ ~ active[Initiator]
    /\ \E j \in 1..Len(inbox[Initiator]) :
          /\ inbox[Initiator][j].type = "tok"
          /\ \/ inbox[Initiator][j].color = "black"
             \/ color[Initiator] = "black"
             \/ counter[Initiator] + inbox[Initiator][j].q > 0
          /\ LET nclock == Merge(Initiator, inbox[Initiator][j].vc)
             IN  /\ clock' = nclock
                 /\ inbox' = [inbox EXCEPT
                        ![Initiator] = RemoveAt(@, j),
                        ![RingOfNodes[Initiator]] =
                            Append(@, [type |-> "tok", q |-> 0, color |-> "white",
                                       vc |-> nclock[Initiator]])]
    /\ color' = [color EXCEPT ![Initiator] = "white"]
    /\ PassesUpd
    /\ UNCHANGED <<active, counter>>

PassToken(n) ==
    /\ n # Initiator
    /\ ~ active[n]
    /\ \E j \in 1..Len(inbox[n]) :
          /\ inbox[n][j].type = "tok"
          /\ LET tkn    == inbox[n][j]
                 nclock == Merge(n, tkn.vc)
             IN  /\ clock' = nclock
                 /\ inbox' = [inbox EXCEPT
                        ![n] = RemoveAt(@, j),
                        ![RingOfNodes[n]] =
                            Append(@, [type  |-> "tok",
                                       q     |-> tkn.q + counter[n],
                                       color |-> IF color[n] = "black"
                                                 THEN "black" ELSE tkn.color,
                                       vc    |-> nclock[n]])]
    /\ color' = [color EXCEPT ![n] = "white"]
    /\ PassesUpd
    /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E n \in Nodes \ {Initiator} : PassToken(n)

SendMsg(n) ==
    /\ active[n]
    /\ counter' = [counter EXCEPT ![n] = @ + 1]
    /\ LET nclock == Tick(n)
       IN  /\ clock' = nclock
           /\ \E m \in Nodes \ {n} :
                 inbox' = [inbox EXCEPT ![m] =
                              Append(@, [type |-> "pl", src |-> n, vc |-> nclock[n]])]
    /\ UNCHANGED <<active, color, passes>>

RecvMsg(n) ==
    /\ \E j \in 1..Len(inbox[n]) :
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
          /\ clock' = Merge(n, inbox[n][j].vc)
    /\ counter' = [counter EXCEPT ![n] = @ - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ color' = [color EXCEPT ![n] = "black"]
    /\ UNCHANGED passes

Deactivate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ clock' = Tick(n)
    /\ UNCHANGED <<color, counter, inbox, passes>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
\* Properties

Safety == TerminationDetected => Termination

\* Termination is detected within at most three token rounds after it occurs.
BoundedRounds == passes <= 3 * N

Liveness == Termination ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ Safety /\ BoundedRounds)
THEOREM Spec => Liveness

-----------------------------------------------------------------------------
\* Refinement mapping to EWD998Chan (nodes 0..N-1, token passed from i to i-1,
\* initiator is node 0).

Node2Nat(n) == IF n = Initiator THEN 0 ELSE N - Dist(n)

Nat2Node(i) == CHOOSE n \in Nodes : Node2Nat(n) = i

Strip(msg) ==
    IF msg.type = "pl"
    THEN [type |-> "pl"]
    ELSE [type |-> "tok", q |-> msg.q, color |-> msg.color]

activeBar  == [i \in 0..(N - 1) |-> active[Nat2Node(i)]]
colorBar   == [i \in 0..(N - 1) |-> color[Nat2Node(i)]]
counterBar == [i \in 0..(N - 1) |-> counter[Nat2Node(i)]]
inboxBar   == [i \in 0..(N - 1) |->
                 [k \in 1..Len(inbox[Nat2Node(i)]) |-> Strip(inbox[Nat2Node(i)][k])]]

EWD998 == INSTANCE EWD998Chan
            WITH N       <- N,
                 active  <- activeBar,
                 color   <- colorBar,
                 counter <- counterBar,
                 inbox   <- inboxBar

EWD998Safe ==
    EWD998!Init /\ [][EWD998!Next]_<<activeBar, colorBar, counterBar, inboxBar>>

THEOREM SafetyRefinement == Spec => EWD998Safe
THEOREM LivenessRefinement == Spec => EWD998!Spec

=============================================================================