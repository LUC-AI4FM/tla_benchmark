------------------------------- MODULE EWD998Chan -------------------------------
(***************************************************************************)
(* Shmuel Safra's termination detection algorithm (EWD 998) on a ring,     *)
(* where each node's message channel (inbox) is a sequence of messages.    *)
(* The token is an explicit message in some node's inbox.                  *)
(***************************************************************************)
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, inbox

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Helper operators *)

RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

IsPl(msg)  == msg.type = "pl"
IsTok(msg) == msg.type = "tok"

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE x \in S : TRUE
                   IN f[x] + SumF(f, S \ {x})

Sum(f) == SumF(f, DOMAIN f)

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

-----------------------------------------------------------------------------
TypeOK ==
  /\ counter \in [Node -> Int]
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ inbox   \in [Node -> Seq(Message)]
  \* There is always exactly one token in the system.
  /\ \E i \in Node : \E j \in 1 .. Len(inbox[i]) : IsTok(inbox[i][j])
  /\ \A i, j \in Node :
       \A k \in 1 .. Len(inbox[i]) :
         \A l \in 1 .. Len(inbox[j]) :
           (IsTok(inbox[i][k]) /\ IsTok(inbox[j][l])) => (i = j /\ k = l)

-----------------------------------------------------------------------------
Init ==
  /\ counter = [i \in Node |-> 0]
  /\ active  \in [Node -> BOOLEAN]
  /\ color   \in [Node -> Color]
  /\ inbox   = [i \in Node |->
                  IF i = 0
                  THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                  ELSE << >>]

InitiateProbe ==
  /\ \E j \in 1 .. Len(inbox[0]) :
       /\ IsTok(inbox[0][j])
       /\ \/ inbox[0][j].color = "black"
          \/ color[0] = "black"
          \/ counter[0] + inbox[0][j].q > 0
       /\ inbox' = [inbox EXCEPT
                      ![0]   = RemoveAt(@, j),
                      ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"])]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter>>

PassToken(i) ==
  /\ ~ active[i]
  /\ \E j \in 1 .. Len(inbox[i]) :
       /\ IsTok(inbox[i][j])
       /\ LET tkn == inbox[i][j]
          IN  inbox' = [inbox EXCEPT
                          ![i]   = RemoveAt(@, j),
                          ![i-1] = Append(@, [type  |-> "tok",
                                              q     |-> tkn.q + counter[i],
                                              color |-> IF color[i] = "black"
                                                        THEN "black"
                                                        ELSE tkn.color])]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter>>

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
       /\ inbox'   = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
       /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
  /\ \E j \in 1 .. Len(inbox[i]) :
       /\ IsPl(inbox[i][j])
       /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ active'  = [active EXCEPT ![i] = TRUE]
  /\ color'   = [color EXCEPT ![i] = "black"]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------
Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Model-checking constraints *)

StateConstraint ==
  /\ \A i \in Node : counter[i] \in -3 .. 3
  /\ \A i \in Node : Len(inbox[i]) <= 3

ActionConstraint ==
  \* Bound the number of in-flight basic messages.
  Sum([i \in Node |-> Len(SelectSeq(inbox'[i], IsPl))]) <= N + 1

-----------------------------------------------------------------------------
(* Refinement mapping to the set/counter based EWD998 model.              *)

aPending == [i \in Node |-> Len(SelectSeq(inbox[i], IsPl))]

aToken ==
  LET i == CHOOSE i \in Node : \E j \in 1 .. Len(inbox[i]) : IsTok(inbox[i][j])
      j == CHOOSE j \in 1 .. Len(inbox[i]) : IsTok(inbox[i][j])
  IN  [pos |-> i, q |-> inbox[i][j].q, color |-> inbox[i][j].color]

avars == <<active, color, counter, aPending, aToken>>

AInit ==
  /\ active   \in [Node -> BOOLEAN]
  /\ color    \in [Node -> Color]
  /\ counter  = [i \in Node |-> 0]
  /\ aPending = [i \in Node |-> 0]
  /\ aToken   = [pos |-> 0, q |-> 0, color |-> "black"]

AInitiateProbe ==
  /\ aToken.pos = 0
  /\ \/ aToken.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + aToken.q > 0
  /\ aToken' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color'  = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, aPending>>

APassToken(i) ==
  /\ ~ active[i]
  /\ aToken.pos = i
  /\ aToken' = [pos   |-> i-1,
                q     |-> aToken.q + counter[i],
                color |-> IF color[i] = "black" THEN "black" ELSE aToken.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, aPending>>

ASystem == AInitiateProbe \/ \E i \in Node \ {0} : APassToken(i)

ASendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E recv \in Node \ {i} :
        aPending' = [aPending EXCEPT ![recv] = @ + 1]
  /\ UNCHANGED <<active, color, aToken>>

ARecvMsg(i) ==
  /\ aPending[i] > 0
  /\ aPending' = [aPending EXCEPT ![i] = @ - 1]
  /\ counter'  = [counter EXCEPT ![i] = @ - 1]
  /\ color'    = [color EXCEPT ![i] = "black"]
  /\ active'   = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED aToken

ADeactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, aPending, aToken>>

AEnvironment == \E i \in Node : ASendMsg(i) \/ ARecvMsg(i) \/ ADeactivate(i)

ANext == ASystem \/ AEnvironment

EWD998Spec == AInit /\ [][ANext]_avars /\ WF_avars(ASystem)

\* Property to check with TLC: EWD998Chan refines EWD998.
Refinement == EWD998Spec

-----------------------------------------------------------------------------
(* Safety and liveness properties *)

Termination ==
  /\ \A i \in Node : ~ active[i]
  /\ \A i \in Node : aPending[i] = 0

terminationDetected ==
  /\ \E j \in 1 .. Len(inbox[0]) :
       /\ IsTok(inbox[0][j])
       /\ inbox[0][j].color = "white"
       /\ inbox[0][j].q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

\* Counters sum up to the number of in-flight basic messages.
CounterInv == Sum(counter) = Sum(aPending)

\* Safety: termination is detected only if the system has terminated.
TerminationDetection == terminationDetected => Termination

\* Once termination is detected, it remains detected (stable).
StableDetection == [](terminationDetected => []terminationDetected)

\* Liveness: termination is eventually detected.
Liveness == Termination ~> terminationDetected

\* Termination is stable.
StableTermination == [](Termination => []Termination)

=============================================================================