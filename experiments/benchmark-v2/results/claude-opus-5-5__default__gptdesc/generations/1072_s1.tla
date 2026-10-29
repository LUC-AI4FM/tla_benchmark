---------------------------- MODULE EWD998ChanID ----------------------------
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Abstract spec: EWD998 with channels on naturally-numbered nodes.        *)
(***************************************************************************)
---------------------------- MODULE EWD998Chan ----------------------------
CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, inbox
vars == <<active, color, counter, inbox>>

RemoveAt(s, k) == SubSeq(s, 1, k-1) \o SubSeq(s, k+1, Len(s))

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ \A i \in Node : \A j \in 1..Len(inbox[i]) :
        inbox[i][j].type \in {"pl", "tok"}

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ inbox = [i \in Node |-> IF i = 0
                 THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                 ELSE << >>]

InitiateProbe ==
  /\ ~ active[0]
  /\ \E j \in 1..Len(inbox[0]) :
       /\ inbox[0][j].type = "tok"
       /\ \/ inbox[0][j].color = "black"
          \/ color[0] = "black"
          \/ counter[0] + inbox[0][j].q > 0
       /\ inbox' = [inbox EXCEPT
                      ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                      ![0] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter>>

PassToken(i) ==
  /\ ~ active[i]
  /\ \E j \in 1..Len(inbox[i]) :
       /\ inbox[i][j].type = "tok"
       /\ LET tkn == inbox[i][j]
          IN inbox' = [inbox EXCEPT
                ![i-1] = Append(@, [type |-> "tok",
                                    q |-> tkn.q + counter[i],
                                    color |-> IF color[i] = "black"
                                              THEN "black" ELSE tkn.color]),
                ![i] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
  /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ \E j \in 1..Len(inbox[i]) :
        /\ inbox[i][j].type = "pl"
        /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

terminationDetected ==
  /\ \E j \in 1..Len(inbox[0]) :
       /\ inbox[0][j].type = "tok"
       /\ inbox[0][j].color = "white"
       /\ inbox[0][j].q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Termination ==
  \A i \in Node : /\ ~ active[i]
                  /\ \A j \in 1..Len(inbox[i]) : inbox[i][j].type # "pl"

Inv == terminationDetected => Termination
Liveness == Termination ~> terminationDetected
=============================================================================