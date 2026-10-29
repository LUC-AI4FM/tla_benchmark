------------------------------- MODULE EWD998ChanID -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Node

ASSUME Node # {} /\ IsFiniteSet(Node)

N == Cardinality(Node)

\* An arbitrary but fixed enumeration of the nodes; it defines the ring.
Order == CHOOSE s \in [1..N -> Node] : \A n \in Node : \E i \in 1..N : s[i] = n

\* The ring is a simple directed cycle: Order[1] -> Order[2] -> ... -> Order[N] -> Order[1]
nb == [ n \in Node |-> LET i == CHOOSE k \in 1..N : Order[k] = n
                       IN Order[(i % N) + 1] ]

Initiator == Order[1]

Color == {"white", "black"}

-----------------------------------------------------------------------------------
VARIABLES
    active,   \* active[n]: is node n performing local work?
    color,    \* color[n]: local color of node n
    counter,  \* counter[n]: payloads sent minus payloads received by n
    inbox,    \* inbox[n]: channel of messages (payloads and token) for n
    clock,    \* clock[n]: vector clock of node n
    qr        \* ghost: number of probe rounds initiated after global quiescence (capped)

vars == <<active, color, counter, inbox, clock, qr>>

-----------------------------------------------------------------------------------
\* Helpers

Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

ZeroVC == [k \in Node |-> 0]

Merge(a, b) == [k \in Node |-> Max(a[k], b[k])]

Tick(v, n) == [v EXCEPT ![n] = @ + 1]

Remove(s, j) == SubSeq(s, 1, j - 1) \o SubSeq(s, j + 1, Len(s))

IsPl(m) == m.type = "pl"

IsTok(m) == m.type = "tok"

PlCount(n) == Len(SelectSeq(inbox[n], IsPl))

SumOf(f) ==
    LET S[i \in 0..N] == IF i = 0 THEN 0 ELSE S[i - 1] + f[Order[i]]
    IN S[N]

InFlight == SumOf([n \in Node |-> PlCount(n)])

TokenAt(n) == { i \in 1..Len(inbox[n]) : IsTok(inbox[n][i]) }

-----------------------------------------------------------------------------------
\* Global termination and its detection

terminated ==
    /\ \A n \in Node : ~active[n]
    /\ \A n \in Node : PlCount(n) = 0

terminationDetected ==
    \E j \in TokenAt(Initiator) :
        LET t == inbox[Initiator][j] IN
        /\ t.color = "white"
        /\ color[Initiator] = "white"
        /\ ~active[Initiator]
        /\ t.q + counter[Initiator] = 0

-----------------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ clock \in [Node -> [Node -> Nat]]
    /\ \A n \in Node : \A i \in 1..Len(inbox[n]) :
          \/ /\ inbox[n][i].type = "pl"
             /\ inbox[n][i].vc \in [Node -> Nat]
          \/ /\ inbox[n][i].type = "tok"
             /\ inbox[n][i].q \in Int
             /\ inbox[n][i].color \in Color
             /\ inbox[n][i].vc \in [Node -> Nat]
    /\ qr \in 0..4

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [n \in Node |-> 0]
    /\ clock = [n \in Node |-> ZeroVC]
    /\ inbox = [n \in Node |->
                  IF n = Initiator
                  THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> ZeroVC] >>
                  ELSE << >>]
    /\ qr = 0

-----------------------------------------------------------------------------------
\* Token actions

InitiateProbe ==
    /\ ~terminationDetected
    /\ \E j \in TokenAt(Initiator) :
        LET t     == inbox[Initiator][j]
            newvc == Tick(Merge(clock[Initiator], t.vc), Initiator)
            tok   == [type |-> "tok", q |-> 0, color |-> "white", vc |-> newvc]
            dest  == nb[Initiator]
            rest  == Remove(inbox[Initiator], j)
        IN
        /\ inbox' = IF dest = Initiator
                    THEN [inbox EXCEPT ![Initiator] = Append(rest, tok)]
                    ELSE [inbox EXCEPT ![Initiator] = rest,
                                       ![dest] = Append(@, tok)]
        /\ clock' = [clock EXCEPT ![Initiator] = newvc]
    /\ color' = [color EXCEPT ![Initiator] = "white"]
    /\ qr' = IF terminated THEN Min(qr + 1, 4) ELSE 0
    /\ UNCHANGED <<active, counter>>

PassToken(n) ==
    /\ n # Initiator
    /\ ~active[n]
    /\ \E j \in TokenAt(n) :
        LET t     == inbox[n][j]
            newvc == Tick(Merge(clock[n], t.vc), n)
            tok   == [type  |-> "tok",
                      q     |-> t.q + counter[n],
                      color |-> IF color[n] = "black" THEN "black" ELSE t.color,
                      vc    |-> newvc]
        IN
        /\ inbox' = [inbox EXCEPT ![n] = Remove(@, j),
                                  ![nb[n]] = Append(@, tok)]
        /\ clock' = [clock EXCEPT ![n] = newvc]
    /\ color' = [color EXCEPT ![n] = "white"]
    /\ UNCHANGED <<active, counter, qr>>

-----------------------------------------------------------------------------------
\* Environment actions

SendMsg(n) ==
    /\ active[n]
    /\ \E r \in Node \ {n} :
        LET newvc == Tick(clock[n], n) IN
        /\ inbox' = [inbox EXCEPT ![r] = Append(@, [type |-> "pl", vc |-> newvc])]
        /\ clock' = [clock EXCEPT ![n] = newvc]
    /\ counter' = [counter EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<active, color, qr>>

RecvMsg(n) ==
    /\ \E j \in 1..Len(inbox[n]) :
        /\ IsPl(inbox[n][j])
        /\ inbox' = [inbox EXCEPT ![n] = Remove(@, j)]
        /\ clock' = [clock EXCEPT ![n] = Tick(Merge(@, inbox[n][j].vc), n)]
    /\ counter' = [counter EXCEPT ![n] = @ - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ color' = [color EXCEPT ![n] = "black"]
    /\ UNCHANGED <<qr>>

Deactivate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ clock' = [clock EXCEPT ![n] = Tick(@, n)]
    /\ UNCHANGED <<color, counter, inbox, qr>>

-----------------------------------------------------------------------------------
System ==
    \/ InitiateProbe
    \/ \E n \in Node \ {Initiator} : PassToken(n)

Environment ==
    \E n \in Node : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

\* The safety-only (fairness-free) behavior specification of the channel protocol.
EWD998ChanSpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Properties

\* Soundness: detection implies global termination.
EWD998Safe == terminationDetected => terminated

\* Counter invariant: sum of counters equals number of in-flight payloads.
CounterInv == SumOf(counter) = InFlight

\* Causality: no in-flight message carries knowledge of its receiver that the
\* receiver itself does not have.
CausalInv ==
    \A n \in Node : \A i \in 1..Len(inbox[n]) :
        inbox[n][i].vc[n] <= clock[n][n]

\* Exactly one token in the system.
TokenInv == SumOf([n \in Node |-> Cardinality(TokenAt(n))]) = 1

\* Liveness: quiescence eventually leads to detection.
EWD998Live == terminated ~> terminationDetected

\* Detection within at most three probe rounds after global quiescence.
Max3TokenRounds == terminated ~> (terminationDetected /\ qr <= 3)

-----------------------------------------------------------------------------------
\* Model-checking support

EWD998ChanStateConstraint ==
    /\ \A n \in Node : counter[n] <= 3
    /\ \A n \in Node : Len(inbox[n]) <= 3

StripMsg(m) ==
    IF IsPl(m) THEN [type |-> "pl"]
    ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

\* Vector clocks are unbounded; exclude them from state fingerprints.
View ==
    << active, color, counter,
       [n \in Node |-> [i \in 1..Len(inbox[n]) |-> StripMsg(inbox[n][i])]],
       qr >>

===================================================================================