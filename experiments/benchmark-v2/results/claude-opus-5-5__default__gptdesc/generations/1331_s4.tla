---- MODULE EWD998Chan ----
EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, inbox

vars == <<active, color, counter, inbox>>

----------------------------------------------------------------------------
(* Helpers *)

RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumF(f, S \ {x})

Rng(a, b) == {i \in Node : a <= i /\ i <= b}

Message == [type : {"tok"}, q : Int, color : Color] \cup [type : {"pl"}]

----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
  /\ counter \in [Node -> Int]
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ DOMAIN inbox = Node
  /\ \A i \in Node : \A k \in 1..Len(inbox[i]) : inbox[i][k] \in Message
  \* There is exactly one token in the system.
  /\ \E i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
  /\ \A i, j \in Node :
       \A k \in 1..Len(inbox[i]) : \A l \in 1..Len(inbox[j]) :
         (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok")
            => (i = j /\ k = l)

----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ inbox = [i \in Node |->
                IF i = 0
                THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                ELSE << >>]

----------------------------------------------------------------------------
(* System actions *)

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

PassToken(i) ==
  /\ ~ active[i]
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "tok"
       /\ LET tkn == inbox[i][j]
          IN inbox' = [inbox EXCEPT
                         ![i-1] = Append(@, [type  |-> "tok",
                                             q     |-> tkn.q + counter[i],
                                             color |-> IF color[i] = "black"
                                                       THEN "black"
                                                       ELSE tkn.color]),
                         ![i]   = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

----------------------------------------------------------------------------
(* Environment actions *)

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
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

----------------------------------------------------------------------------
(* Specification *)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

----------------------------------------------------------------------------
(* Model-checking constraints *)

MaxCounter == 3
MaxInbox   == 3

StateConstraint ==
  \A i \in Node :
     /\ counter[i] <= MaxCounter
     /\ counter[i] >= -MaxCounter
     /\ Len(inbox[i]) <= MaxInbox

ActionConstraint ==
  \A i \in Node : Len(inbox'[i]) <= MaxInbox

----------------------------------------------------------------------------
(* Refinement mapping to the set-based EWD998 model *)

tokenBar ==
  LET n  == CHOOSE i \in Node :
              \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
      k  == CHOOSE j \in 1..Len(inbox[n]) : inbox[n][j].type = "tok"
      tk == inbox[n][k]
  IN [pos |-> n, q |-> tk.q, color |-> tk.color]

pendingBar ==
  [i \in Node |-> Len(SelectSeq(inbox[i], LAMBDA msg : msg.type = "pl"))]

absVars == <<active, color, counter, pendingBar, tokenBar>>

(* Abstract EWD998 specification expressed over the mapped state *)

A_Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pendingBar = [i \in Node |-> 0]
  /\ tokenBar = [pos |-> 0, q |-> 0, color |-> "black"]

A_InitiateProbe ==
  /\ tokenBar.pos = 0
  /\ \/ tokenBar.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + tokenBar.q > 0
  /\ tokenBar' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pendingBar>>

A_PassToken(i) ==
  /\ ~ active[i]
  /\ tokenBar.pos = i
  /\ tokenBar' = [pos   |-> i-1,
                  q     |-> tokenBar.q + counter[i],
                  color |-> IF color[i] = "black" THEN "black" ELSE tokenBar.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pendingBar>>

A_System == A_InitiateProbe \/ \E i \in Node \ {0} : A_PassToken(i)

A_SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E recv \in Node \ {i} :
       pendingBar' = [pendingBar EXCEPT ![recv] = @ + 1]
  /\ UNCHANGED <<active, color, tokenBar>>

A_RecvMsg(i) ==
  /\ pendingBar[i] > 0
  /\ pendingBar' = [pendingBar EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED tokenBar

A_Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pendingBar, tokenBar>>

A_Environment ==
  \E i \in Node : A_SendMsg(i) \/ A_RecvMsg(i) \/ A_Deactivate(i)

A_Next == A_System \/ A_Environment

EWD998Spec == A_Init /\ [][A_Next]_absVars /\ WF_absVars(A_System)

----------------------------------------------------------------------------
(* Safety properties *)

Termination ==
  \A i \in Node : ~ active[i] /\ pendingBar[i] = 0

terminationDetected ==
  \E j \in 1..Len(inbox[0]) :
     /\ inbox[0][j].type = "tok"
     /\ inbox[0][j].color = "white"
     /\ inbox[0][j].q + counter[0] = 0
     /\ color[0] = "white"
     /\ ~ active[0]

TerminationDetection ==
  terminationDetected => Termination

\* Safra's invariant (EWD998), stated over the refinement mapping.
Inv ==
  /\ SumF(pendingBar, Node) = SumF(counter, Node)
  /\ \/ /\ \A i \in Rng(tokenBar.pos + 1, N-1) : ~ active[i]
        /\ IF tokenBar.pos = N-1
           THEN tokenBar.q = 0
           ELSE tokenBar.q = SumF(counter, Rng(tokenBar.pos + 1, N-1))
     \/ SumF(counter, Rng(0, tokenBar.pos)) + tokenBar.q > 0
     \/ \E i \in Rng(0, tokenBar.pos) : color[i] = "black"
     \/ tokenBar.color = "black"

----------------------------------------------------------------------------
(* Temporal properties *)

\* Once terminated, the system stays terminated.
TerminationStable == [][Termination => Termination']_vars

\* Termination is eventually detected.
Liveness == Termination ~> terminationDetected

\* EWD998Chan refines EWD998.
Refinement == EWD998Spec

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => []Inv
THEOREM Spec => Liveness
THEOREM Spec => EWD998Spec
====