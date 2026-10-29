---------------------------- MODULE EWD998ChanID ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Node
ASSUME NodeAssumption == IsFiniteSet(Node) /\ Node # {}

N == Cardinality(Node)

\* The distinguished initiator; which one is irrelevant as long as it is fixed.
Initiator == CHOOSE n \in Node : TRUE

\* An enumeration of the nodes that starts at the initiator.
Nat2Node ==
  CHOOSE f \in [0..N-1 -> Node] :
    /\ f[0] = Initiator
    /\ \A i, j \in 0..N-1 : i # j => f[i] # f[j]

Node2Nat == [n \in Node |-> CHOOSE i \in 0..N-1 : Nat2Node[i] = n]

\* Organize the nodes in a ring: RingOfNodes[n] is the node to which n
\* passes the token.
RingOfNodes ==
  [n \in Node |-> IF Node2Nat[n] = 0
                  THEN Nat2Node[N-1]
                  ELSE Nat2Node[Node2Nat[n] - 1]]

Color == {"white", "black"}

VARIABLES
  active,
  color,
  counter,
  inbox,
  clock

vars == <<active, color, counter, inbox, clock>>

------------------------------------------------------------------------------
\* Helpers

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

Merge(a, b) == [m \in Node |-> IF a[m] > b[m] THEN a[m] ELSE b[m]]

Inc(v, n) == [v EXCEPT ![n] = @ + 1]

ZeroVC == [m \in Node |-> 0]

TokenMsg == [type : {"tok"}, q : Int, color : Color,
             vc : [Node -> Nat], rounds : Nat]
BasicMsg == [type : {"pl"}, src : Node, vc : [Node -> Nat]]

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ inbox \in [Node -> Seq(TokenMsg \cup BasicMsg)]
  /\ clock \in [Node -> [Node -> Nat]]

------------------------------------------------------------------------------
\* Termination and its detection.

Termination ==
  \A n \in Node :
    /\ ~ active[n]
    /\ \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

terminationDetected ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
       /\ inbox[Initiator][j].type = "tok"
       /\ inbox[Initiator][j].color = "white"
       /\ inbox[Initiator][j].q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

------------------------------------------------------------------------------

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [n \in Node |-> 0]
  /\ inbox = [n \in Node |->
                IF n = Initiator
                THEN << [type |-> "tok", q |-> 0, color |-> "black",
                         vc |-> ZeroVC, rounds |-> 0] >>
                ELSE << >>]
  /\ clock = [n \in Node |-> ZeroVC]

\* The field "rounds" is a ghost counting token rounds started after
\* termination of the underlying computation.
InitiateProbe ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
       LET tok == inbox[Initiator][j] IN
       /\ tok.type = "tok"
       /\ \/ tok.color = "black"
          \/ color[Initiator] = "black"
          \/ counter[Initiator] + tok.q > 0
       /\ LET c == Inc(Merge(clock[Initiator], tok.vc), Initiator) IN
          /\ clock' = [clock EXCEPT ![Initiator] = c]
          /\ inbox' = [inbox EXCEPT
                          ![Initiator] = RemoveAt(@, j),
                          ![RingOfNodes[Initiator]] =
                             Append(@, [type |-> "tok", q |-> 0,
                                        color |-> "white", vc |-> c,
                                        rounds |-> IF Termination
                                                   THEN tok.rounds + 1
                                                   ELSE 0])]
  /\ color' = [color EXCEPT ![Initiator] = "white"]
  /\ UNCHANGED <<active, counter>>

PassToken(n) ==
  /\ ~ active[n]
  /\ \E j \in 1..Len(inbox[n]) :
       LET tok == inbox[n][j] IN
       /\ tok.type = "tok"
       /\ LET c == Inc(Merge(clock[n], tok.vc), n) IN
          /\ clock' = [clock EXCEPT ![n] = c]
          /\ inbox' = [inbox EXCEPT
                          ![n] = RemoveAt(@, j),
                          ![RingOfNodes[n]] =
                             Append(@, [tok EXCEPT
                                          !.q = tok.q + counter[n],
                                          !.color = IF color[n] = "black"
                                                    THEN "black"
                                                    ELSE tok.color,
                                          !.vc = c])]
  /\ color' = [color EXCEPT ![n] = "white"]
  /\ UNCHANGED <<active, counter>>

System ==
  \/ InitiateProbe
  \/ \E n \in Node \ {Initiator} : PassToken(n)

------------------------------------------------------------------------------

SendMsg(n) ==
  /\ active[n]
  /\ \E r \in Node \ {n} :
       LET c == Inc(clock[n], n) IN
       /\ clock' = [clock EXCEPT ![n] = c]
       /\ inbox' = [inbox EXCEPT ![r] =
                      Append(@, [type |-> "pl", src |-> n, vc |-> c])]
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<active, color>>

RecvMsg(n) ==
  /\ \E j \in 1..Len(inbox[n]) :
       /\ inbox[n][j].type = "pl"
       /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
       /\ clock' = [clock EXCEPT ![n] = Inc(Merge(clock[n], inbox[n][j].vc), n)]
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ color' = [color EXCEPT ![n] = "black"]

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ clock' = [clock EXCEPT ![n] = Inc(clock[n], n)]
  /\ UNCHANGED <<color, counter, inbox>>

Environment ==
  \E n \in Node : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

------------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

------------------------------------------------------------------------------

EWD998ChanStateConstraint ==
  \A n \in Node :
    /\ counter[n] <= 3
    /\ counter[n] >= -3
    /\ Len(inbox[n]) <= 3

StripMsg(m) ==
  IF m.type = "tok"
  THEN [type |-> "tok", q |-> m.q, color |-> m.color]
  ELSE [type |-> "pl"]

\* The view abstracts from the (unbounded) vector clocks.
View ==
  <<active, color, counter,
    [n \in Node |-> [j \in 1..Len(inbox[n]) |->
        IF inbox[n][j].type = "tok"
        THEN [type |-> "tok", q |-> inbox[n][j].q,
              color |-> inbox[n][j].color, rounds |-> inbox[n][j].rounds]
        ELSE [type |-> "pl"]]]>>

------------------------------------------------------------------------------

EWD998Safe == terminationDetected => Termination

EWD998Live == Termination ~> terminationDetected

TokenRoundsBounded ==
  \A n \in Node : \A j \in 1..Len(inbox[n]) :
    inbox[n][j].type = "tok" => inbox[n][j].rounds <= 3

\* Termination is detected within at most three token rounds after the
\* system has terminated.
Max3TokenRounds ==
  Termination ~> (terminationDetected /\ TokenRoundsBounded)

THEOREM Spec => Max3TokenRounds

------------------------------------------------------------------------------
\* Refinement mapping to EWD998Chan (nodes 0..N-1, initiator 0).

EWD998Chan == INSTANCE EWD998Chan WITH
  N <- N,
  active  <- [i \in 0..N-1 |-> active[Nat2Node[i]]],
  color   <- [i \in 0..N-1 |-> color[Nat2Node[i]]],
  counter <- [i \in 0..N-1 |-> counter[Nat2Node[i]]],
  inbox   <- [i \in 0..N-1 |->
                [j \in 1..Len(inbox[Nat2Node[i]]) |->
                   StripMsg(inbox[Nat2Node[i]][j])]]

EWD998ChanSpec == EWD998Chan!Spec

THEOREM Spec => EWD998ChanSpec
THEOREM Spec => []EWD998Safe
THEOREM Spec => EWD998Live

=============================================================================