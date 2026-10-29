------------------------------- MODULE EWD998Chan -------------------------------
EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

TokenMsg   == [type : {"tok"}, q : Int, color : Color]
PayloadMsg == [type : {"pl"}]
Message    == TokenMsg \union PayloadMsg

VARIABLES
  active,   \* active[i]: process i is active
  color,    \* color[i]: process i is black or white
  counter,  \* counter[i]: #payload sends minus #payload receives at i
  inbox     \* inbox[i]: channel (sequence of messages) towards node i

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Helpers *)

RemoveAt(s, k) == SubSeq(s, 1, k-1) \o SubSeq(s, k+1, Len(s))

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + SumF(f, S \ {x})

Rng(a, b) == { i \in Node : a <= i /\ i <= b }

TokenPositions(i) == { j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok" }
PayloadPositions(i) == { j \in 1..Len(inbox[i]) : inbox[i][j].type = "pl" }

\* number of in-flight payload messages per node
pending == [ i \in Node |-> Cardinality(PayloadPositions(i)) ]

-----------------------------------------------------------------------------
TypeOK ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ inbox   \in [Node -> Seq(Message)]
  \* the token is unique in the whole system
  /\ Cardinality({ i \in Node : TokenPositions(i) # {} }) = 1
  /\ \A i \in Node : Cardinality(TokenPositions(i)) <= 1

-----------------------------------------------------------------------------
Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter = [ i \in Node |-> 0 ]
  /\ inbox   = [ i \in Node |->
                   IF i = 0
                   THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                   ELSE << >> ]

\* Node 0 holds the token and the round failed: start a new round.
InitiateProbe ==
  /\ \E j \in 1..Len(inbox[0]) :
       /\ inbox[0][j].type = "tok"
       /\ \/ inbox[0][j].color = "black"
          \/ color[0] = "black"
          \/ counter[0] + inbox[0][j].q > 0
       /\ inbox' = [inbox EXCEPT
                      ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                      ![0]   = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter>>

\* A passive node i (i # 0) holding the token forwards it to node i-1.
PassToken(i) ==
  /\ i # 0
  /\ ~ active[i]
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "tok"
       /\ LET tkn == inbox[i][j]
          IN  inbox' = [inbox EXCEPT
                ![i-1] = Append(@, [type  |-> "tok",
                                    q     |-> tkn.q + counter[i],
                                    color |-> IF color[i] = "black"
                                              THEN "black" ELSE tkn.color]),
                ![i]   = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

\* An active node sends a payload message to another node.
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
       inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<active, color>>

\* A node receives a payload message: it becomes active and black.
RecvMsg(i) ==
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "pl"
       /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ active'  = [active  EXCEPT ![i] = TRUE]
  /\ color'   = [color   EXCEPT ![i] = "black"]

\* An active node becomes passive.
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, inbox>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Bounds for model checking *)

MaxChan    == 3
MaxCounter == 3

StateConstraint ==
  /\ \A i \in Node : Len(inbox[i]) <= MaxChan
  /\ \A i \in Node : counter[i] \in -MaxCounter .. MaxCounter

ActionConstraint ==
  /\ \A i \in Node : Len(inbox'[i]) <= MaxChan
  /\ \A i \in Node : counter'[i] \in -MaxCounter .. MaxCounter

-----------------------------------------------------------------------------
(* Properties *)

tokenHolder == CHOOSE i \in Node : TokenPositions(i) # {}
token       == inbox[tokenHolder][CHOOSE j \in TokenPositions(tokenHolder) : TRUE]

Quiescent ==
  /\ \A i \in Node : ~ active[i]
  /\ \A i \in Node : pending[i] = 0

terminationDetected ==
  /\ \E j \in 1..Len(inbox[0]) :
       /\ inbox[0][j].type = "tok"
       /\ inbox[0][j].color = "white"
       /\ inbox[0][j].q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

TokenUnique ==
  Cardinality({ <<i, j>> \in Node \X Nat :
                  j \in TokenPositions(i) }) = 1

\* Termination-detection soundness.
TerminationDetection == terminationDetected => Quiescent

\* Safra's invariant (counters track in-flight payloads; coloring reflects activity).
EWD998Inv ==
  /\ SumF(pending, Node) = SumF(counter, Node)
  /\ \/ /\ \A i \in Rng(tokenHolder + 1, N-1) : ~ active[i]
        /\ IF tokenHolder = N-1
           THEN token.q = 0
           ELSE token.q = SumF(counter, Rng(tokenHolder + 1, N-1))
     \/ SumF(counter, Rng(0, tokenHolder)) + token.q > 0
     \/ \E i \in Rng(0, tokenHolder) : color[i] = "black"
     \/ token.color = "black"

\* Liveness: quiescence is eventually detected.
Liveness == Quiescent ~> terminationDetected

Stop == TerminationDetection

PostCondition == N \in Nat \ {0}

THEOREM Spec => [](TypeOK /\ TokenUnique /\ EWD998Inv /\ TerminationDetection)
THEOREM Spec => Liveness
=============================================================================