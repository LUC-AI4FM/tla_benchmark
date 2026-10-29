------------------------------- MODULE EWD998ChanID -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

\* Five nodes identified by strings rather than integers.
Node == {"n1", "n2", "n3", "n4", "n5"}

Nodes == Node

N == Cardinality(Nodes)

\* The initiator of fresh tokens.
Initiator == CHOOSE n \in Nodes : TRUE

RECURSIVE Iter(_, _, _)
Iter(r, n, k) == IF k = 0 THEN n ELSE Iter(r, r[n], k - 1)

IsSimpleCycle(S, r) ==
    LET x == CHOOSE s \in S : TRUE
    IN { Iter(r, x, k) : k \in 0..(Cardinality(S) - 1) } = S

\* Organize the nodes in a ring.
RingOfNodes == CHOOSE r \in [ Nodes -> Nodes ] : IsSimpleCycle(Nodes, r)

Color == {"white", "black"}

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

Max(a, b) == IF a > b THEN a ELSE b

VARIABLES
    active,
    color,
    counter,
    inbox,
    clock,
    passes

vars == <<active, color, counter, inbox, clock, passes>>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ counter \in [Nodes -> Int]
    /\ passes \in Nat

Terminated ==
    /\ \A n \in Nodes : ~ active[n]
    /\ \A n \in Nodes : \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

TerminationDetected ==
    /\ \E j \in 1..Len(inbox[Initiator]) :
        /\ inbox[Initiator][j].type = "tok"
        /\ inbox[Initiator][j].color = "white"
        /\ counter[Initiator] + inbox[Initiator][j].q = 0
    /\ color[Initiator] = "white"
    /\ ~ active[Initiator]

Tick(n) == [clock EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN clock[n][m] + 1
                                                       ELSE clock[n][m]]]

Merge(n, vc) == [clock EXCEPT ![n] = [m \in Nodes |->
                        IF m = n THEN clock[n][m] + 1
                        ELSE Max(clock[n][m], vc[m])]]

Init ==
    /\ counter = [n \in Nodes |-> 0]
    /\ inbox = [n \in Nodes |-> IF n = Initiator
                                THEN << [type |-> "tok", q |-> 0, color |-> "black",
                                         vc |-> [m \in Nodes |-> 0]] >>
                                ELSE <<>>]
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ clock = [n \in Nodes |-> [m \in Nodes |-> 0]]
    /\ passes = 0

InitiateProbe(n) ==
    /\ n = Initiator
    /\ \E j \in 1..Len(inbox[n]) :
        /\ inbox[n][j].type = "tok"
        /\ \/ inbox[n][j].color = "black"
           \/ color[n] = "black"
           \/ counter[n] + inbox[n][j].q # 0
        /\ LET newclk == Merge(n, inbox[n][j].vc)
           IN /\ clock' = newclk
              /\ inbox' = [inbox EXCEPT
                             ![RingOfNodes[n]] = Append(@, [type |-> "tok", q |-> 0,
                                                    color |-> "white", vc |-> newclk[n]]),
                             ![n] = RemoveAt(@, j)]
    /\ color' = [color EXCEPT ![n] = "white"]
    /\ passes' = IF Terminated THEN passes + 1 ELSE passes
    /\ UNCHANGED <<active, counter>>

PassToken(n) ==
    /\ n # Initiator
    /\ ~ active[n]
    /\ \E j \in 1..Len(inbox[n]) :
        /\ inbox[n][j].type = "tok"
        /\ LET tkn == inbox[n][j]
               newclk == Merge(n, tkn.vc)
           IN /\ clock' = newclk
              /\ inbox' = [inbox EXCEPT
                             ![RingOfNodes[n]] = Append(@, [type |-> "tok",
                                    q |-> tkn.q + counter[n],
                                    color |-> IF color[n] = "black" THEN "black" ELSE tkn.color,
                                    vc |-> newclk[n]]),
                             ![n] = RemoveAt(@, j)]
    /\ color' = [color EXCEPT ![n] = "white"]
    /\ passes' = IF Terminated THEN passes + 1 ELSE passes
    /\ UNCHANGED <<active, counter>>

System(n) == InitiateProbe(n) \/ PassToken(n)

SendMsg(n) ==
    /\ active[n]
    /\ counter' = [counter EXCEPT ![n] = @ + 1]
    /\ LET newclk == Tick(n)
       IN /\ clock' = newclk
          /\ \E recv \in Nodes \ {n} :
                inbox' = [inbox EXCEPT ![recv] = Append(@, [type |-> "pl", src |-> n,
                                                             vc |-> newclk[n]])]
    /\ UNCHANGED <<active, color, passes>>

RecvMsg(n) ==
    /\ \E j \in 1..Len(inbox[n]) :
        /\ inbox[n][j].type = "pl"
        /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
        /\ clock' = Merge(n, inbox[n][j].vc)
    /\ counter' = [counter EXCEPT ![n] = @ - 1]
    /\ color' = [color EXCEPT ![n] = "black"]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ UNCHANGED passes

Deactivate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ clock' = Tick(n)
    /\ UNCHANGED <<color, inbox, counter, passes>>

Environment(n) == SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

Next == \E n \in Nodes : System(n) \/ Environment(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : System(n))

-----------------------------------------------------------------------------

EWD998ChanStateConstraint ==
    /\ \A n \in Nodes : counter[n] < 3 /\ Len(inbox[n]) < 3
    /\ passes <= 3 * N + 1

EWD998Safe == TerminationDetected => Terminated

EWD998Live == Terminated ~> TerminationDetected

Max3TokenRounds == passes <= 3 * N

Strip(m) == IF m.type = "pl" THEN [type |-> "pl"]
            ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

StripSeq(s) == [j \in 1..Len(s) |-> Strip(s[j])]

View == <<active, color, counter, [n \in Nodes |-> StripSeq(inbox[n])], passes>>

-----------------------------------------------------------------------------
\* Refinement mapping to the integer-indexed EWD998Chan.

Nat2Node(i) == Iter(RingOfNodes, Initiator, (N - i) % N)

Node2Nat(n) == CHOOSE i \in 0..(N - 1) : Nat2Node(i) = n

Idx == 0..(N - 1)

AActive  == [i \in Idx |-> active[Nat2Node(i)]]
AColor   == [i \in Idx |-> color[Nat2Node(i)]]
ACounter == [i \in Idx |-> counter[Nat2Node(i)]]
AInbox   == [i \in Idx |-> StripSeq(inbox[Nat2Node(i)])]

avars == <<AActive, AColor, ACounter, AInbox>>

AInit ==
    /\ ACounter = [i \in Idx |-> 0]
    /\ AInbox = [i \in Idx |-> IF i = 0
                               THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                               ELSE <<>>]
    /\ AActive \in [Idx -> BOOLEAN]
    /\ AColor \in [Idx -> Color]

AInitiateToken ==
    /\ \E j \in 1..Len(AInbox[0]) :
        /\ AInbox[0][j].type = "tok"
        /\ \/ AInbox[0][j].color = "black"
           \/ AColor[0] = "black"
           \/ ACounter[0] + AInbox[0][j].q # 0
        /\ AInbox' = [AInbox EXCEPT
                        ![N - 1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                        ![0] = RemoveAt(@, j)]
    /\ AColor' = [AColor EXCEPT ![0] = "white"]
    /\ UNCHANGED <<AActive, ACounter>>

APassToken(i) ==
    /\ i # 0
    /\ ~ AActive[i]
    /\ \E j \in 1..Len(AInbox[i]) :
        /\ AInbox[i][j].type = "tok"
        /\ LET tkn == AInbox[i][j]
           IN AInbox' = [AInbox EXCEPT
                           ![i - 1] = Append(@, [type |-> "tok",
                                   q |-> tkn.q + ACounter[i],
                                   color |-> IF AColor[i] = "black" THEN "black" ELSE tkn.color]),
                           ![i] = RemoveAt(@, j)]
    /\ AColor' = [AColor EXCEPT ![i] = "white"]
    /\ UNCHANGED <<AActive, ACounter>>

ASystem == AInitiateToken \/ \E i \in Idx \ {0} : APassToken(i)

ASendMsg(i) ==
    /\ AActive[i]
    /\ ACounter' = [ACounter EXCEPT ![i] = @ + 1]
    /\ \E k \in Idx \ {i} :
          AInbox' = [AInbox EXCEPT ![k] = Append(@, [type |-> "pl"])]
    /\ UNCHANGED <<AActive, AColor>>

ARecvMsg(i) ==
    /\ \E j \in 1..Len(AInbox[i]) :
        /\ AInbox[i][j].type = "pl"
        /\ AInbox' = [AInbox EXCEPT ![i] = RemoveAt(@, j)]
    /\ ACounter' = [ACounter EXCEPT ![i] = @ - 1]
    /\ AColor' = [AColor EXCEPT ![i] = "black"]
    /\ AActive' = [AActive EXCEPT ![i] = TRUE]

ADeactivate(i) ==
    /\ AActive[i]
    /\ AActive' = [AActive EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<AColor, AInbox, ACounter>>

AEnvironment == \E i \in Idx : ASendMsg(i) \/ ARecvMsg(i) \/ ADeactivate(i)

ANext == ASystem \/ AEnvironment

EWD998ChanSpec == AInit /\ [][ANext]_avars /\ WF_avars(ASystem)

=============================================================================