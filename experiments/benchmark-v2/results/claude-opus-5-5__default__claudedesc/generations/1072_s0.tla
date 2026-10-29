--------------------------- MODULE EWD998ChanID ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes

ASSUME IsFiniteSet(Nodes) /\ Cardinality(Nodes) > 1

N == Cardinality(Nodes)

Max(a, b) == IF a > b THEN a ELSE b

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

IsSimpleCycle(S, r) ==
  LET F[i \in 1..Cardinality(S)] ==
        IF i = 1 THEN r ELSE [s \in S |-> r[F[i - 1][s]]]
  IN \A s \in S : {F[j][s] : j \in 1..Cardinality(S)} = S

RingOfNodes ==
  CHOOSE r \in [Nodes -> Nodes] : IsSimpleCycle(Nodes, r)

Initiator == CHOOSE n \in Nodes : TRUE

nat2node[i \in 0..N-1] ==
  IF i = 0 THEN Initiator
  ELSE CHOOSE m \in Nodes : RingOfNodes[m] = nat2node[i - 1]

node2nat == [n \in Nodes |-> CHOOSE i \in 0..N-1 : nat2node[i] = n]

Color == {"white", "black"}

VARIABLES active, color, counter, inbox, clock, passes

vars == <<active, color, counter, inbox, clock, passes>>

ZeroClock == [m \in Nodes |-> 0]

Message ==
       [type : {"pl"}, src : Nodes, vc : [Nodes -> Nat]]
  \cup [type : {"tok"}, q : Int, color : Color, vc : [Nodes -> Nat]]

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter \in [Nodes -> Int]
  /\ inbox \in [Nodes -> Seq(Message)]
  /\ clock \in [Nodes -> [Nodes -> Nat]]
  /\ passes \in Nat
  /\ \E n \in Nodes :
       Cardinality({ j \in 1..Len(inbox[n]) : inbox[n][j].type = "tok" }) = 1

-----------------------------------------------------------------------------
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

Tick(n) == [clock EXCEPT ![n] = [clock[n] EXCEPT ![n] = @ + 1]]

MergeTick(n, vc) ==
  [clock EXCEPT ![n] = [m \in Nodes |->
       IF m = n THEN clock[n][n] + 1 ELSE Max(clock[n][m], vc[m])]]

Termination ==
  /\ \A n \in Nodes : ~ active[n]
  /\ \A n \in Nodes : \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

-----------------------------------------------------------------------------
InitiateProbe(n) ==
  /\ n = Initiator
  /\ \E j \in 1..Len(inbox[n]) :
       /\ inbox[n][j].type = "tok"
       /\ \/ inbox[n][j].color = "black"
          \/ color[n] = "black"
          \/ counter[n] + inbox[n][j].q # 0
       /\ clock' = MergeTick(n, inbox[n][j].vc)
       /\ inbox' = [inbox EXCEPT
                      ![RingOfNodes[n]] = Append(@, [type |-> "tok", q |-> 0,
                                                     color |-> "white",
                                                     vc |-> clock'[n]]),
                      ![n] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![n] = "white"]
  /\ passes' = IF Termination THEN passes + 1 ELSE 0
  /\ UNCHANGED <<active, counter>>

PassToken(n) ==
  /\ n # Initiator
  /\ ~ active[n]
  /\ \E j \in 1..Len(inbox[n]) :
       /\ inbox[n][j].type = "tok"
       /\ clock' = MergeTick(n, inbox[n][j].vc)
       /\ LET tkn == inbox[n][j]
          IN inbox' = [inbox EXCEPT
                         ![RingOfNodes[n]] =
                            Append(@, [type |-> "tok",
                                       q |-> tkn.q + counter[n],
                                       color |-> IF color[n] = "black"
                                                 THEN "black" ELSE tkn.color,
                                       vc |-> clock'[n]]),
                         ![n] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![n] = "white"]
  /\ passes' = IF Termination THEN passes + 1 ELSE 0
  /\ UNCHANGED <<active, counter>>

System(n) == InitiateProbe(n) \/ PassToken(n)

-----------------------------------------------------------------------------
SendMsg(n) ==
  /\ active[n]
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ clock' = Tick(n)
  /\ \E recv \in Nodes \ {n} :
       inbox' = [inbox EXCEPT ![recv] = Append(@, [type |-> "pl", src |-> n,
                                                   vc |-> clock'[n]])]
  /\ UNCHANGED <<active, color, passes>>

RecvMsg(n) ==
  /\ \E j \in 1..Len(inbox[n]) :
       /\ inbox[n][j].type = "pl"
       /\ clock' = MergeTick(n, inbox[n][j].vc)
       /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j)]
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  /\ color' = [color EXCEPT ![n] = "black"]
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<passes>>

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ clock' = Tick(n)
  /\ UNCHANGED <<color, inbox, counter, passes>>

Environment(n) == SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

-----------------------------------------------------------------------------
Next == \E n \in Nodes : System(n) \/ Environment(n)

SystemAll == \E n \in Nodes : System(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(SystemAll)

-----------------------------------------------------------------------------
terminationDetected ==
  /\ \E j \in 1..Len(inbox[Initiator]) :
       /\ inbox[Initiator][j].type = "tok"
       /\ inbox[Initiator][j].color = "white"
       /\ inbox[Initiator][j].q + counter[Initiator] = 0
  /\ color[Initiator] = "white"
  /\ ~ active[Initiator]

EWD998Safe == terminationDetected => Termination

EWD998Live == Termination ~> terminationDetected

Max3TokenRounds == passes <= 3 * N

-----------------------------------------------------------------------------
(* Refinement mapping to the integer-indexed EWD998Chan module. *)

MapMsg(m) ==
  IF m.type = "pl" THEN [type |-> "pl"]
  ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

EWD998ChanActive  == [i \in 0..N-1 |-> active[nat2node[i]]]
EWD998ChanColor   == [i \in 0..N-1 |-> color[nat2node[i]]]
EWD998ChanCounter == [i \in 0..N-1 |-> counter[nat2node[i]]]
EWD998ChanInbox   == [i \in 0..N-1 |->
                        LET s == inbox[nat2node[i]]
                        IN [j \in 1..Len(s) |-> MapMsg(s[j])]]

EWD998Chan == INSTANCE EWD998Chan
                WITH N <- N,
                     active <- EWD998ChanActive,
                     color <- EWD998ChanColor,
                     counter <- EWD998ChanCounter,
                     inbox <- EWD998ChanInbox

EWD998ChanSpec == EWD998Chan!Spec

THEOREM Spec => []TypeOK
THEOREM Spec => []EWD998Safe
THEOREM Spec => EWD998Live
THEOREM Spec => []Max3TokenRounds
THEOREM Spec => EWD998ChanSpec
=============================================================================