------------------------------- MODULE EWD998Chan -------------------------------
EXTENDS Integers, Sequences, FiniteSets, Naturals, TLC

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,
  color,
  counter,
  inbox

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + SumSet(f, S \ {x})

Rng(a, b) == a .. b

-----------------------------------------------------------------------------
TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message == TokenMsg \cup BasicMsg

TypeOK ==
  /\ counter \in [Nodes -> Int]
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ inbox \in [Nodes -> Seq(Message)]
  \* There is exactly one token in the system.
  /\ \E i \in Nodes : \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"
  /\ \A i, j \in Nodes : \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
        inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok" => (i = j /\ k = l)

-----------------------------------------------------------------------------
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ counter = [i \in Nodes |-> 0]
  /\ inbox = [i \in Nodes |->
                IF i = 0
                THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                ELSE << >>]

InitiateProbe ==
  /\ \E j \in 1 .. Len(inbox[0]) :
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
  /\ \E j \in 1 .. Len(inbox[i]) :
       /\ inbox[i][j].type = "tok"
       /\ LET tkn == inbox[i][j]
          IN  inbox' = [inbox EXCEPT
                          ![i-1] = Append(@, [type |-> "tok",
                                              q |-> tkn.q + counter[i],
                                              color |-> IF color[i] = "black"
                                                        THEN "black"
                                                        ELSE tkn.color]),
                          ![i] = RemoveAt(@, j)]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == \/ InitiateProbe
          \/ \E i \in Nodes \ {0} : PassToken(i)

-----------------------------------------------------------------------------
SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Nodes \ {i} :
        inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
  /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ \E j \in 1 .. Len(inbox[i]) :
        /\ inbox[i][j].type = "pl"
        /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Refinement mapping to the set-based EWD998 model *)

pending ==
  [i \in Nodes |-> Len(SelectSeq(inbox[i], LAMBDA m : m.type = "pl"))]

tokenPos ==
  CHOOSE i \in Nodes : \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"

tokenMsg ==
  LET j == CHOOSE j \in 1 .. Len(inbox[tokenPos]) : inbox[tokenPos][j].type = "tok"
  IN  inbox[tokenPos][j]

token == [pos |-> tokenPos, q |-> tokenMsg.q, color |-> tokenMsg.color]

\* The invariant of EWD998, expressed via the refinement mapping.
EWD998Inv ==
  /\ SumSet(counter, Nodes) = SumSet(pending, Nodes)
  /\ \/ /\ \A i \in Rng(token.pos + 1, N-1) : active[i] = FALSE
        /\ IF token.pos = N-1
           THEN token.q = 0
           ELSE token.q = SumSet(counter, Rng(token.pos + 1, N-1))
     \/ SumSet(counter, Rng(0, token.pos)) + token.q > 0
     \/ \E i \in Rng(0, token.pos) : color[i] = "black"
     \/ token.color = "black"

Termination ==
  \A i \in Nodes : ~ active[i] /\ pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

\* Safety: termination is only detected when the system has terminated.
Stop == terminationDetected => Termination

TerminationDetection == terminationDetected => Termination

\* Liveness: termination is eventually detected.
Liveness == Termination ~> terminationDetected

\* Once detected, termination stays detected (system stays quiescent).
Stable == [](terminationDetected => []terminationDetected)

-----------------------------------------------------------------------------
(* Model-checking bounds *)

StateConstraint ==
  \A i \in Nodes :
     /\ counter[i] \in -3 .. 3
     /\ Len(inbox[i]) <= 3

ActionConstraint ==
  \* Do not explore beyond the state in which termination has been detected.
  ~ terminationDetected

PostCondition ==
  TRUE

=============================================================================