------------------------------ MODULE EWD998Chan ------------------------------
(***************************************************************************)
(* Shmuel Safra's termination detection algorithm (EWD 998) on a ring.    *)
(* In this variant the message channels are modeled as sequences (the     *)
(* inbox of each node).  The token is a message in some node's inbox.     *)
(* The spec refines a set/counter based model (EWD998) via a refinement   *)
(* mapping, which is stated in this module so that it stands alone.       *)
(***************************************************************************)
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* activity status of each node
    color,    \* color of each node
    counter,  \* sent minus received basic messages, per node
    inbox     \* sequence of messages (basic messages and the token), per node

vars == <<active, color, counter, inbox>>

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

\* Remove the i-th element of sequence s.
RemoveAt(s, i) ==
    [j \in 1 .. (Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant.  Exactly one token exists in the system.               *)
(***************************************************************************)
TypeOK ==
    /\ counter \in [Node -> Int]
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ inbox   \in [Node -> Seq(Message)]
    /\ \E i \in Node : \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"
    /\ \A i, j \in Node :
         \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
            (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok")
                => (i = j /\ k = l)

-----------------------------------------------------------------------------
Init ==
    /\ counter = [i \in Node |-> 0]
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ inbox = [i \in Node |->
                  IF i = 0
                  THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                  ELSE << >>]

(***************************************************************************)
(* Node 0 initiates a new probe if the previous round was inconclusive.   *)
(***************************************************************************)
InitiateProbe ==
    /\ ~ active[0]
    /\ \E j \in 1 .. Len(inbox[0]) :
         /\ inbox[0][j].type = "tok"
         /\ \/ inbox[0][j].color = "black"
            \/ color[0] = "black"
            \/ counter[0] + inbox[0][j].q > 0
         /\ inbox' = [inbox EXCEPT
                        ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"]),
                        ![0]   = RemoveAt(@, j)]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter>>

(***************************************************************************)
(* A passive node i # 0 holding the token passes it on to node i-1.       *)
(***************************************************************************)
PassToken(i) ==
    /\ ~ active[i]
    /\ \E j \in 1 .. Len(inbox[i]) :
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
(***************************************************************************)
(* Environment actions: sending, receiving basic messages, deactivation. *)
(***************************************************************************)
SendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Node \ {i} :
         inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
    /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
    /\ \E j \in 1 .. Len(inbox[i]) :
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

-----------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the set/counter based model EWD998.              *)
(***************************************************************************)
pendingBar ==
    [i \in Node |-> Cardinality({j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "pl"})]

tokenBar ==
    LET pos == CHOOSE i \in Node :
                  \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"
        idx == CHOOSE j \in 1 .. Len(inbox[pos]) : inbox[pos][j].type = "tok"
    IN  [pos |-> pos, q |-> inbox[pos][idx].q, color |-> inbox[pos][idx].color]

avars == <<active, color, counter, pendingBar, tokenBar>>

\* --- Abstract EWD998 spec, expressed over the mapped state ---------------
AInit ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pendingBar = [i \in Node |-> 0]
    /\ tokenBar = [pos |-> 0, q |-> 0, color |-> "black"]

AInitiateProbe ==
    /\ tokenBar.pos = 0
    /\ ~ active[0]
    /\ \/ tokenBar.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + tokenBar.q > 0
    /\ tokenBar' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter, pendingBar>>

APassToken(i) ==
    /\ ~ active[i]
    /\ tokenBar.pos = i
    /\ tokenBar' = [pos   |-> i - 1,
                    q     |-> tokenBar.q + counter[i],
                    color |-> IF color[i] = "black" THEN "black" ELSE tokenBar.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter, pendingBar>>

ASystem == AInitiateProbe \/ \E i \in Node \ {0} : APassToken(i)

ASendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E recv \in Node \ {i} :
         pendingBar' = [pendingBar EXCEPT ![recv] = @ + 1]
    /\ UNCHANGED <<active, color, tokenBar>>

ARecvMsg(i) ==
    /\ pendingBar[i] > 0
    /\ pendingBar' = [pendingBar EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED tokenBar

ADeactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, pendingBar, tokenBar>>

AEnvironment == \E i \in Node : ASendMsg(i) \/ ARecvMsg(i) \/ ADeactivate(i)

ANext == ASystem \/ AEnvironment

EWD998Spec == AInit /\ [][ANext]_avars /\ WF_avars(ASystem)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
Termination ==
    \A i \in Node : ~ active[i] /\ pendingBar[i] = 0

terminationDetected ==
    /\ tokenBar.pos = 0
    /\ tokenBar.color = "white"
    /\ tokenBar.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

\* Safety: termination is detected only when the system has terminated.
TerminationDetection == terminationDetected => Termination

\* Counters sum up to the number of messages in flight.
CounterInv ==
    LET Sum[S \in SUBSET Node] ==
            IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN  counter[x] - pendingBar[x] + Sum[S \ {x}]
    IN  Sum[Node] = 0

\* Liveness: once terminated, termination is eventually detected.
Liveness == Termination ~> terminationDetected

\* Termination is stable.
TerminationStable == [][Termination => Termination']_vars

\* The spec implements the abstract EWD998 model.
EWD998Refinement == EWD998Spec

THEOREM Spec => [](TypeOK /\ TerminationDetection /\ CounterInv)
THEOREM Spec => Liveness
THEOREM Spec => EWD998Refinement

-----------------------------------------------------------------------------
(***************************************************************************)
(* Constraints to bound the state space for TLC.                          *)
(***************************************************************************)
MaxCounter == 3
MaxInbox   == 3

StateConstraint ==
    \A i \in Node :
        /\ counter[i] \in -MaxCounter .. MaxCounter
        /\ Len(inbox[i]) <= MaxInbox

\* Disallow steps that would push counters out of bound.
ActionConstraint ==
    \A i \in Node : counter'[i] \in -MaxCounter .. MaxCounter

=============================================================================