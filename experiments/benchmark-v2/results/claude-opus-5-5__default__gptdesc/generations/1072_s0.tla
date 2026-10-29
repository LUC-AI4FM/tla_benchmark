------------------------------- MODULE EWD998ChanID -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes
ASSUME NodesAssumption == IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

Initiator == CHOOSE n \in Nodes : TRUE

RECURSIVE Iter(_, _, _)
Iter(r, n, k) == IF k = 0 THEN n ELSE Iter(r, r[n], k - 1)

IsRing(r) ==
    /\ { Iter(r, Initiator, k) : k \in 0..(N - 1) } = Nodes
    /\ Iter(r, Initiator, N) = Initiator

RingOfNodes == CHOOSE r \in [Nodes -> Nodes] : IsRing(r)

Nat2Node == [ i \in 0..(N - 1) |-> Iter(RingOfNodes, Initiator, (N - i) % N) ]
Node2Nat == [ n \in Nodes |-> CHOOSE i \in 0..(N - 1) : Nat2Node[i] = n ]

Color == {"white", "black"}

Max(a, b) == IF a > b THEN a ELSE b

RemoveAt(s, i) == [ k \in 1..(Len(s) - 1) |-> IF k < i THEN s[k] ELSE s[k + 1] ]

VARIABLES
    active,
    color,
    counter,
    inbox,
    clock,
    rnd

vars == <<active, color, counter, inbox, clock, rnd>>

TokenMsg == [type : {"tok"}, q : Int, color : Color, vc : [Nodes -> Nat]]
BasicMsg == [type : {"pl"}, vc : [Nodes -> Nat]]
Message  == TokenMsg \cup BasicMsg

TypeOK ==
    /\ counter \in [Nodes -> Int]
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ inbox \in [Nodes -> Seq(Message)]
    /\ clock \in [Nodes -> [Nodes -> Nat]]
    /\ rnd \in Nat
    /\ \E i \in Nodes : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
    /\ \A i, j \in Nodes :
         \A k \in 1..Len(inbox[i]) : \A l \in 1..Len(inbox[j]) :
            (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok")
                => (i = j /\ k = l)

-----------------------------------------------------------------------------------

Tick(n) == [ clock EXCEPT ![n][n] = @ + 1 ]

Merge(n, vc) ==
    [ clock EXCEPT ![n] = [ m \in Nodes |->
                              IF m = n THEN Max(clock[n][m], vc[m]) + 1
                                       ELSE Max(clock[n][m], vc[m]) ] ]

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

-----------------------------------------------------------------------------------

Init ==
    /\ counter = [ n \in Nodes |-> 0 ]
    /\ inbox = [ n \in Nodes |->
                   IF n = Initiator
                   THEN << [type |-> "tok", q |-> 0, color |-> "black",
                            vc |-> [ m \in Nodes |-> 0 ]] >>
                   ELSE << >> ]
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ clock = [ n \in Nodes |-> [ m \in Nodes |-> 0 ] ]
    /\ rnd = 0

InitiateProbe ==
    /\ \E j \in 1..Len(inbox[Initiator]) :
         /\ inbox[Initiator][j].type = "tok"
         /\ \/ inbox[Initiator][j].color = "black"
            \/ color[Initiator] = "black"
            \/ counter[Initiator] + inbox[Initiator][j].q > 0
         /\ LET newclock == Merge(Initiator, inbox[Initiator][j].vc)
            IN /\ clock' = newclock
               /\ inbox' = [ inbox EXCEPT
                               ![RingOfNodes[Initiator]] =
                                   Append(@, [type |-> "tok", q |-> 0,
                                              color |-> "white",
                                              vc |-> newclock[Initiator]]),
                               ![Initiator] = RemoveAt(@, j) ]
    /\ color' = [ color EXCEPT ![Initiator] = "white" ]
    /\ rnd' = IF Termination THEN rnd + 1 ELSE 0
    /\ UNCHANGED <<active, counter>>

PassToken(n) ==
    /\ n # Initiator
    /\ ~ active[n]
    /\ \E j \in 1..Len(inbox[n]) :
         /\ inbox[n][j].type = "tok"
         /\ LET tkn      == inbox[n][j]
                newclock == Merge(n, tkn.vc)
            IN /\ clock' = newclock
               /\ inbox' = [ inbox EXCEPT
                               ![RingOfNodes[n]] =
                                   Append(@, [type |-> "tok",
                                              q |-> tkn.q + counter[n],
                                              color |-> IF color[n] = "black"
                                                        THEN "black"
                                                        ELSE tkn.color,
                                              vc |-> newclock[n]]),
                               ![n] = RemoveAt(@, j) ]
    /\ color' = [ color EXCEPT ![n] = "white" ]
    /\ UNCHANGED <<active, counter, rnd>>

System == InitiateProbe \/ \E n \in Nodes \ {Initiator} : PassToken(n)

-----------------------------------------------------------------------------------

SendMsg(n) ==
    /\ active[n]
    /\ counter' = [ counter EXCEPT ![n] = @ + 1 ]
    /\ LET newclock == Tick(n)
       IN /\ clock' = newclock
          /\ \E m \in Nodes \ {n} :
               inbox' = [ inbox EXCEPT ![m] =
                            Append(@, [type |-> "pl", vc |-> newclock[n]]) ]
    /\ UNCHANGED <<active, color, rnd>>

RecvMsg(n) ==
    /\ counter' = [ counter EXCEPT ![n] = @ - 1 ]
    /\ color' = [ color EXCEPT ![n] = "black" ]
    /\ active' = [ active EXCEPT ![n] = TRUE ]
    /\ \E j \in 1..Len(inbox[n]) :
         /\ inbox[n][j].type = "pl"
         /\ inbox' = [ inbox EXCEPT ![n] = RemoveAt(@, j) ]
         /\ clock' = Merge(n, inbox[n][j].vc)
    /\ UNCHANGED <<rnd>>

Deactivate(n) ==
    /\ active[n]
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ clock' = Tick(n)
    /\ UNCHANGED <<color, inbox, counter, rnd>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

-----------------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------------

Safety == terminationDetected => Termination

Liveness == Termination ~> terminationDetected

BoundedRounds == rnd <= 3

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => []BoundedRounds

-----------------------------------------------------------------------------------

StripMsg(m) ==
    IF m.type = "pl"
    THEN [type |-> "pl"]
    ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

EWD998Chan == INSTANCE EWD998Chan WITH
    N       <- N,
    active  <- [ i \in 0..(N - 1) |-> active[Nat2Node[i]] ],
    color   <- [ i \in 0..(N - 1) |-> color[Nat2Node[i]] ],
    counter <- [ i \in 0..(N - 1) |-> counter[Nat2Node[i]] ],
    inbox   <- [ i \in 0..(N - 1) |->
                   [ k \in 1..Len(inbox[Nat2Node[i]]) |->
                       StripMsg(inbox[Nat2Node[i]][k]) ] ]

EWD998ChanSafety == EWD998Chan!Init /\ [][EWD998Chan!Next]_EWD998Chan!vars

EWD998ChanLiveness == EWD998Chan!Spec

THEOREM Spec => EWD998ChanSafety
THEOREM Spec => EWD998ChanLiveness

===================================================================================