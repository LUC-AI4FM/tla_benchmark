------------------------------- MODULE EWD998Chan -------------------------------
(***************************************************************************)
(* Shmuel Safra's termination detection algorithm (EWD 998) on a ring,     *)
(* where message channels are modeled as sequences (inboxes).  Both basic  *)
(* "payload" messages and the circulating token travel through the         *)
(* inboxes.  A refinement mapping to the set/counter based EWD998 model    *)
(* (pending messages per node and a single token record) is defined       *)
(* inline below.                                                           *)
(***************************************************************************)
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,   \* activity status of each node
  color,    \* color of each node
  counter,  \* number of sent minus number of received messages per node
  inbox     \* inbox (message channel) of each node

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

\* Remove the i-th element of sequence s.
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

TypeOK ==
  /\ counter \in [Node -> Int]
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ inbox \in [Node -> Seq(Message)]
  \* There is always exactly one token in the system.
  /\ \E i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
  /\ \A i, j \in Node :
       \A k \in 1..Len(inbox[i]) : \A l \in 1..Len(inbox[j]) :
         (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok") => (i = j /\ k = l)

-----------------------------------------------------------------------------

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ inbox = [i \in Node |->
                IF i = 0
                THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                ELSE << >>]

InitiateProbe ==
  /\ \E j \in 1..Len(inbox[0]) :
       \* The token is at node 0.
       /\ inbox[0][j].type = "tok"
       \* The previous round was inconclusive.
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
          IN inbox' = [inbox EXCEPT
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

-----------------------------------------------------------------------------

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

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* State and action constraints bounding the state space for TLC.          *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
  /\ \A i \in DOMAIN counter : counter[i] < 3

ActionConstraint ==
  \A i \in Node : counter'[i] - counter[i] \in {-1, 0, 1}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the EWD998 model (pending counts and one token).  *)
(***************************************************************************)
tokenBar ==
  LET i == CHOOSE i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
      j == CHOOSE j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
  IN [pos |-> i, q |-> inbox[i][j].q, color |-> inbox[i][j].color]

pendingBar ==
  [i \in Node |-> Cardinality({j \in 1..Len(inbox[i]) : inbox[i][j].type = "pl"})]

absVars == <<active, color, counter, pendingBar, tokenBar>>

AbsTypeOK ==
  /\ pendingBar \in [Node -> Nat]
  /\ tokenBar \in [pos : Node, q : Int, color : Color]

AbsInit ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pendingBar = [i \in Node |-> 0]
  /\ tokenBar = [pos |-> 0, q |-> 0, color |-> "black"]

AbsInitiateProbe ==
  /\ tokenBar.pos = 0
  /\ \/ tokenBar.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + tokenBar.q # 0
  /\ tokenBar' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pendingBar>>

AbsPassToken(i) ==
  /\ ~ active[i]
  /\ tokenBar.pos = i
  /\ tokenBar' = [pos   |-> i-1,
                  q     |-> tokenBar.q + counter[i],
                  color |-> IF color[i] = "black" THEN "black" ELSE tokenBar.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pendingBar>>

AbsSendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} : pendingBar' = [pendingBar EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, tokenBar>>

AbsRecvMsg(i) ==
  /\ pendingBar[i] > 0
  /\ pendingBar' = [pendingBar EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED tokenBar

AbsDeactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pendingBar, tokenBar>>

AbsSystem == \/ AbsInitiateProbe
             \/ \E i \in Node \ {0} : AbsPassToken(i)

AbsEnvironment == \E i \in Node : AbsSendMsg(i) \/ AbsRecvMsg(i) \/ AbsDeactivate(i)

AbsNext == AbsSystem \/ AbsEnvironment

EWD998Spec == AbsInit /\ [][AbsNext]_absVars /\ WF_absVars(AbsSystem)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety and liveness properties.                                         *)
(***************************************************************************)
Termination ==
  \A i \in Node : ~ active[i] /\ pendingBar[i] = 0

terminationDetected ==
  /\ tokenBar.pos = 0
  /\ tokenBar.color = "white"
  /\ tokenBar.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

\* The sum of all counters equals the number of in-flight payload messages.
CounterInv ==
  LET Sum[S \in SUBSET Node] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE x \in S : TRUE
             IN counter[x] + pendingBar[x] * 0 + Sum[S \ {x}]
      PSum[S \in SUBSET Node] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE x \in S : TRUE
             IN pendingBar[x] + PSum[S \ {x}]
  IN Sum[Node] = PSum[Node]

\* Safety: termination is detected only if the system has terminated.
TerminationDetection ==
  terminationDetected => Termination

\* Liveness: if the system terminates, termination is eventually detected.
Liveness ==
  Termination ~> terminationDetected

\* Once terminated, the system stays terminated.
TerminationStable ==
  [][Termination => Termination']_vars

\* The channel-based spec refines the EWD998 model.
RefinesEWD998 == EWD998Spec

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
THEOREM Spec => RefinesEWD998
=============================================================================