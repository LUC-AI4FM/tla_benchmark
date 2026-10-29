------------------------------- MODULE EWD998Chan -------------------------------
EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,
  color,
  counter,
  inbox

vars == <<active, color, counter, inbox>>

(* Remove the element at position i from sequence s. *)
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

TypeOK ==
  /\ counter \in [Node -> Int]
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ inbox   \in [Node -> Seq(Message)]
  \* There is exactly one token in the whole ring.
  /\ \E i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
  /\ \A i, j \in Node :
        \A k \in 1..Len(inbox[i]) : \A l \in 1..Len(inbox[j]) :
          (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok")
             => (i = j /\ k = l)

------------------------------------------------------------------------------

Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ inbox   = [i \in Node |->
                   IF i = 0
                   THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                   ELSE << >>]

------------------------------------------------------------------------------
(* System actions: token passing protocol.                                    *)

InitiateProbe ==
  /\ \E j \in 1..Len(inbox[0]) :
       /\ inbox[0][j].type = "tok"
       /\ \/ inbox[0][j].color = "black"
          \/ color[0] = "black"
          \/ counter[0] + inbox[0][j].q # 0
       /\ inbox' = [inbox EXCEPT
                      ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                      ![0]   = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter>>

PassToken(i) ==
  /\ ~ active[i]
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "tok"
       /\ LET tkn == inbox[i][j]
          IN  inbox' = [inbox EXCEPT
                          ![i-1] = Append(@, [type  |-> "tok",
                                              q     |-> tkn.q + counter[i],
                                              color |-> IF color[i] = "black"
                                                        THEN "black"
                                                        ELSE tkn.color]),
                          ![i]   = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

------------------------------------------------------------------------------
(* Environment actions: payload messages and deactivation.                   *)

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
  /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "pl"
       /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color'   = [color EXCEPT ![i] = "black"]
  /\ active'  = [active EXCEPT ![i] = TRUE]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

------------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

------------------------------------------------------------------------------
(* Bound the state space for model checking.                                  *)

StateConstraint ==
  /\ \A i \in Node : counter[i] <= 3 /\ Len(inbox[i]) < 3

------------------------------------------------------------------------------
(* Refinement mapping to the set-based EWD998 specification.                  *)

TokenPos ==
  CHOOSE i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"

TokenIdx ==
  CHOOSE j \in 1..Len(inbox[TokenPos]) : inbox[TokenPos][j].type = "tok"

TokenMap ==
  [pos   |-> TokenPos,
   q     |-> inbox[TokenPos][TokenIdx].q,
   color |-> inbox[TokenPos][TokenIdx].color]

PendingMap ==
  [i \in Node |-> Len(SelectSeq(inbox[i], LAMBDA msg : msg.type = "pl"))]

EWD998 == INSTANCE EWD998 WITH token <- TokenMap, pending <- PendingMap

EWD998Spec == EWD998!Spec

EWD998Inv == EWD998!Inv

THEOREM Spec => EWD998Spec

THEOREM Spec => [](TypeOK /\ EWD998Inv)

=============================================================================