------------------------------- MODULE EWD998Chan -------------------------------
(***************************************************************************)
(* Shmuel Safra's termination detection algorithm (EWD 998) on a ring,     *)
(* with message channels modeled as sequences (inboxes). The token is a    *)
(* message in some node's inbox. The spec gives a refinement mapping to    *)
(* the set-based EWD998 model, which is written out inline below.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,   \* activation status of nodes
    color,    \* color of nodes
    counter,  \* nb of sent messages - nb of received messages per node
    inbox     \* channels (sequences of messages) per node

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Helper: remove the i-th element of a sequence. *)
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

IsPl(m)  == m.type = "pl"
IsTok(m) == m.type = "tok"

TypeOK ==
    /\ counter \in [Node -> Int]
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ inbox \in [Node -> Seq(Message)]
    \* There is always a token in some inbox ...
    /\ \E i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
    \* ... and there is at most one token.
    /\ \A i, j \in Node :
         \A k \in 1..Len(inbox[i]) : \A l \in 1..Len(inbox[j]) :
            (inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok")
                => (i = j /\ k = l)

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
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ color' = [color EXCEPT ![i] = "black"]

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* State and action constraints to bound the state space for TLC. *)
StateConstraint ==
    /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
    /\ \A i \in DOMAIN counter : counter[i] <= 3 /\ counter[i] >= -3
    /\ \A i \in Node : \A j \in 1..Len(inbox[i]) :
          inbox[i][j].type = "tok" => (inbox[i][j].q <= 3 /\ inbox[i][j].q >= -3)

ActionConstraint ==
    \* Do not send a message if the counter is already at its bound.
    \A i \in Node : counter'[i] <= 3 /\ counter'[i] >= -3

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the set-based EWD998 model.                       *)
(***************************************************************************)
TPos == CHOOSE i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"

Tok  == LET j == CHOOSE j \in 1..Len(inbox[TPos]) : inbox[TPos][j].type = "tok"
        IN  inbox[TPos][j]

EWD998pending == [i \in Node |-> Len(SelectSeq(inbox[i], IsPl))]

EWD998token == [pos |-> TPos, q |-> Tok.q, color |-> Tok.color]

EWD998vars == <<active, color, counter, EWD998pending, EWD998token>>

(* The abstract EWD998 specification expressed over the mapped variables. *)
EWD998Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ EWD998pending = [i \in Node |-> 0]
    /\ EWD998token = [pos |-> 0, q |-> 0, color |-> "black"]

EWD998InitiateProbe ==
    /\ EWD998token.pos = 0
    /\ \/ EWD998token.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + EWD998token.q > 0
    /\ EWD998token' = [pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter>>
    /\ EWD998pending' = EWD998pending

EWD998PassToken(i) ==
    /\ ~ active[i]
    /\ EWD998token.pos = i
    /\ EWD998token' = [pos   |-> i-1,
                       q     |-> EWD998token.q + counter[i],
                       color |-> IF color[i] = "black" THEN "black"
                                 ELSE EWD998token.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter>>
    /\ EWD998pending' = EWD998pending

EWD998System == EWD998InitiateProbe \/ \E i \in Node \ {0} : EWD998PassToken(i)

EWD998SendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Node \ {i} :
         EWD998pending' = [EWD998pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED <<active, color>>
    /\ EWD998token' = EWD998token

EWD998RecvMsg(i) ==
    /\ EWD998pending[i] > 0
    /\ EWD998pending' = [EWD998pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ EWD998token' = EWD998token

EWD998Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter>>
    /\ EWD998pending' = EWD998pending
    /\ EWD998token' = EWD998token

EWD998Environment ==
    \E i \in Node : EWD998SendMsg(i) \/ EWD998RecvMsg(i) \/ EWD998Deactivate(i)

EWD998Next == EWD998System \/ EWD998Environment

EWD998Spec ==
    EWD998Init /\ [][EWD998Next]_EWD998vars /\ WF_EWD998vars(EWD998System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties (stated via the refinement mapping).             *)
(***************************************************************************)
Termination ==
    \A i \in Node : ~ active[i] /\ EWD998pending[i] = 0

TerminationDetected ==
    /\ EWD998token.pos = 0
    /\ EWD998token.color = "white"
    /\ EWD998token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

\* Safety: termination is only detected when the system has terminated.
TDSafe == TerminationDetected => Termination

Inv == TypeOK /\ TDSafe

\* Once terminated, the system stays terminated.
TerminationStable == [](Termination => []Termination)

\* Liveness: termination is eventually detected.
Liveness == Termination ~> TerminationDetected

\* Refinement: EWD998Chan implements EWD998.
EWD998Refinement == EWD998Spec

THEOREM Spec => []TypeOK
THEOREM Spec => []TDSafe
THEOREM Spec => Liveness
THEOREM Spec => EWD998Spec
=============================================================================