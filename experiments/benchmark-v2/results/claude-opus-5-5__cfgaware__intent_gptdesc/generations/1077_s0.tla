------------------------------- MODULE EWD998Chan -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

TokenMsg   == [type : {"tok"}, q : Int, color : Color]
PayloadMsg == [type : {"pl"}]
Message    == TokenMsg \cup PayloadMsg

VARIABLES
    active,     \* active[i]: process i is active
    color,      \* color[i]: process i is black (sent work since token) or white
    counter,    \* counter[i]: #sent - #received payload messages of process i
    inbox       \* inbox[i]: sequence of messages in transit to process i

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Helpers *)

RemoveAt(s, j) == SubSeq(s, 1, j - 1) \o SubSeq(s, j + 1, Len(s))

IsPl(m)  == m.type = "pl"
IsTok(m) == m.type = "tok"

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + SumSet(f, S \ {x})

Sum(f) == SumSet(f, Node)

Rng(a, b) == {i \in Node : a <= i /\ i <= b}

TokenPositions ==
    {<<i, j>> \in Node \X Nat : j \in 1 .. Len(inbox[i]) /\ IsTok(inbox[i][j])}

HasToken(i) == \E j \in 1 .. Len(inbox[i]) : IsTok(inbox[i][j])

(* Refinement mapping to the abstract EWD998 variables *)
pendingBar == [i \in Node |-> Len(SelectSeq(inbox[i], IsPl))]

tokenBar ==
    LET pos == CHOOSE i \in Node : HasToken(i)
        idx == CHOOSE j \in 1 .. Len(inbox[pos]) : IsTok(inbox[pos][j])
        tok == inbox[pos][idx]
    IN  [pos |-> pos, q |-> tok.q, color |-> tok.color]

-----------------------------------------------------------------------------
(* Concrete specification with channels *)

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ inbox   = [i \in Node |->
                    IF i = 0
                    THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                    ELSE << >>]

InitiateProbe ==
    /\ ~ active[0]
    /\ \E j \in 1 .. Len(inbox[0]) :
         /\ IsTok(inbox[0][j])
         /\ \/ inbox[0][j].color = "black"
            \/ color[0] = "black"
            \/ counter[0] + inbox[0][j].q # 0
         /\ inbox' = [inbox EXCEPT
                         ![0]   = RemoveAt(@, j),
                         ![N-1] = Append(@, [type |-> "tok", q |-> 0, color |-> "white"])]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, counter>>

PassToken(i) ==
    /\ i # 0
    /\ ~ active[i]
    /\ \E j \in 1 .. Len(inbox[i]) :
         /\ IsTok(inbox[i][j])
         /\ LET tok == inbox[i][j]
            IN  inbox' = [inbox EXCEPT
                             ![i]   = RemoveAt(@, j),
                             ![i-1] = Append(@, [type  |-> "tok",
                                                 q     |-> tok.q + counter[i],
                                                 color |-> IF color[i] = "black"
                                                           THEN "black"
                                                           ELSE tok.color])]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter>>

SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node :
         inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, color>>

RecvMsg(i) ==
    /\ \E j \in 1 .. Len(inbox[i]) :
         /\ IsPl(inbox[i][j])
         /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j)]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color'   = [color EXCEPT ![i] = "black"]
    /\ active'  = [active EXCEPT ![i] = TRUE]

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, inbox>>

System      == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)
Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Model-checking helpers *)

StateConstraint ==
    \A i \in Node :
        /\ counter[i] <= 3
        /\ counter[i] >= -3
        /\ Len(inbox[i]) <= 3

Alias ==
    [ active   |-> active,
      color    |-> color,
      counter  |-> counter,
      inbox    |-> inbox,
      pending  |-> pendingBar,
      token    |-> tokenBar ]

-----------------------------------------------------------------------------
(* Invariants and properties *)

TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ inbox   \in [Node -> Seq(Message)]

AtMostOneToken == Cardinality(TokenPositions) <= 1
ExactlyOneToken == Cardinality(TokenPositions) = 1

\* Conservation: sum of local counters equals number of in-flight payload messages
CounterConsistency == Sum(counter) = Sum(pendingBar)

Termination ==
    \A i \in Node : ~ active[i] /\ pendingBar[i] = 0

terminationDetected ==
    /\ ~ active[0]
    /\ color[0] = "white"
    /\ \E j \in 1 .. Len(inbox[0]) :
         /\ IsTok(inbox[0][j])
         /\ inbox[0][j].color = "white"
         /\ inbox[0][j].q + counter[0] = 0

Safe == terminationDetected => Termination

\* Safra's invariant
Inv ==
    /\ Sum(pendingBar) = Sum(counter)
    /\ \/ /\ \A i \in Rng(tokenBar.pos + 1, N - 1) : ~ active[i]
          /\ IF tokenBar.pos = N - 1
             THEN tokenBar.q = 0
             ELSE tokenBar.q = SumSet(counter, Rng(tokenBar.pos + 1, N - 1))
       \/ SumSet(counter, Rng(0, tokenBar.pos)) + tokenBar.q > 0
       \/ \E i \in Rng(0, tokenBar.pos) : color[i] = "black"
       \/ tokenBar.color = "black"

\* Monotonicity of token metadata during a round
TokenColorMonotone ==
    [][ (tokenBar.color = "black" /\ tokenBar'.pos # N - 1)
          => tokenBar'.color = "black" ]_vars

TokenQAccumulates ==
    [][ \A i \in Node \ {0} :
          (tokenBar.pos = i /\ tokenBar'.pos = i - 1)
            => tokenBar'.q = tokenBar.q + counter[i] ]_vars

Liveness == Termination ~> terminationDetected

-----------------------------------------------------------------------------
(* Abstract EWD998 specification expressed via the refinement mapping *)

AInit ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pendingBar = [i \in Node |-> 0]
    /\ tokenBar = [pos |-> 0, q |-> 0, color |-> "black"]

AInitiateProbe ==
    /\ tokenBar.pos = 0
    /\ ~ active[0]
    /\ \/ tokenBar.color = "black"
       \/ color[0] = "black"
       \/ counter[0] + tokenBar.q # 0
    /\ tokenBar' = [pos |-> N - 1, q |-> 0, color |-> "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ pendingBar' = pendingBar
    /\ UNCHANGED <<active, counter>>

APassToken(i) ==
    /\ i # 0
    /\ ~ active[i]
    /\ tokenBar.pos = i
    /\ tokenBar' = [pos   |-> i - 1,
                    q     |-> tokenBar.q + counter[i],
                    color |-> IF color[i] = "black" THEN "black" ELSE tokenBar.color]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ pendingBar' = pendingBar
    /\ UNCHANGED <<active, counter>>

ASendMsg(i) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ \E j \in Node : pendingBar' = [pendingBar EXCEPT ![j] = @ + 1]
    /\ tokenBar' = tokenBar
    /\ UNCHANGED <<active, color>>

ARecvMsg(i) ==
    /\ pendingBar[i] > 0
    /\ pendingBar' = [pendingBar EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color'   = [color EXCEPT ![i] = "black"]
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ tokenBar' = tokenBar

ADeactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pendingBar' = pendingBar
    /\ tokenBar' = tokenBar
    /\ UNCHANGED <<color, counter>>

ANext ==
    \/ AInitiateProbe
    \/ \E i \in Node \ {0} : APassToken(i)
    \/ \E i \in Node : ASendMsg(i) \/ ARecvMsg(i) \/ ADeactivate(i)

EWD998Spec ==
    AInit /\ [][ANext]_<<active, color, counter, pendingBar, tokenBar>>

THEOREM Spec => [](TypeOK /\ AtMostOneToken /\ CounterConsistency /\ Inv /\ Safe)
THEOREM Spec => Liveness
THEOREM Spec => EWD998Spec

=============================================================================