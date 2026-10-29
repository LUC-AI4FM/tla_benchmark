------------------------------ MODULE SafraTerminationChan ------------------------------
(***************************************************************************)
(* Safra's termination-detection algorithm (EWD 998) on a unidirectional  *)
(* ring of N processes with asynchronous, bounded FIFO channels.          *)
(*                                                                         *)
(* The ring is 0 -> N-1 -> N-2 -> ... -> 1 -> 0. A process forwards the   *)
(* token to its predecessor. Process 0 is the initiator.                  *)
(*                                                                         *)
(* Messages are either payload messages [type |-> "pl"] or the token      *)
(* [type |-> "tok", q |-> Int, color |-> Color]. Each process has an      *)
(* inbox, a FIFO sequence of messages. A message leaves a channel only    *)
(* through a receive action: a payload receive or token consumption.      *)
(*                                                                         *)
(* Coloring: a process turns black when it takes part in payload traffic  *)
(* that the token's counter may miss in the current round. This model     *)
(* uses Safra's sound rule: a process turns black upon receipt of a       *)
(* payload. It turns white again when the token visits it. The invariant  *)
(* SafraInv states the precise meaning of the colors.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,          \* number of processes in the ring
    MaxChan     \* bound on payload messages per channel (for model checking)

ASSUME NAssump    == N \in Nat \ {0}
ASSUME ChanAssump == MaxChan \in Nat \ {0}

Node      == 0 .. N-1
Initiator == 0
Color     == {"white", "black"}

TokenMsg   == [type : {"tok"}, q : Int, color : Color]
PayloadMsg == [type : {"pl"}]
Msg        == TokenMsg \cup PayloadMsg

VARIABLES
    active,     \* active[i] : process i is active
    color,      \* color[i]  : local color of process i
    counter,    \* counter[i]: (#payloads sent) - (#payloads received) by i
    inbox       \* inbox[i]  : FIFO channel of messages destined for i

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET y == CHOOSE z \in S : TRUE
         IN  f[y] + SumSet(f, S \ {y})

Rng(a, b) == {i \in Node : a <= i /\ i <= b}

PlCount(s)  == Cardinality({k \in 1 .. Len(s) : s[k].type = "pl"})
TokCount(s) == Cardinality({k \in 1 .. Len(s) : s[k].type = "tok"})

InTransit == SumSet([i \in Node |-> PlCount(inbox[i])], Node)
NumTokens == SumSet([i \in Node |-> TokCount(inbox[i])], Node)

HoldsToken(i) == inbox[i] # <<>> /\ Head(inbox[i]).type = "tok"

TokenAt(i)  == TokCount(inbox[i]) > 0
TokenPos    == CHOOSE i \in Node : TokenAt(i)
TheToken    == LET s == inbox[TokenPos]
               IN  s[CHOOSE k \in 1 .. Len(s) : s[k].type = "tok"]

-----------------------------------------------------------------------------
TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ inbox   \in [Node -> Seq(Msg)]

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ inbox   = [i \in Node |->
                    IF i = Initiator
                    THEN << [type |-> "tok", q |-> 0, color |-> "black"] >>
                    ELSE << >>]

-----------------------------------------------------------------------------
(* Token actions *)

\* The initiator holds the returned token and cannot conclude termination.
\* It starts a new round with a white token whose counter is zero.
InitiateProbe ==
    /\ HoldsToken(Initiator)
    /\ LET tok == Head(inbox[Initiator]) IN
         /\ \/ tok.color = "black"
            \/ color[Initiator] = "black"
            \/ tok.q + counter[Initiator] # 0
         /\ inbox' = [inbox EXCEPT
                        ![N-1]       = Append(@, [type  |-> "tok",
                                                  q     |-> 0,
                                                  color |-> "white"]),
                        ![Initiator] = Tail(@)]
    /\ color' = [color EXCEPT ![Initiator] = "white"]
    /\ UNCHANGED <<active, counter>>

\* A passive non-initiator holding the token forwards it to its predecessor.
\* It adds its counter to the token and blackens the token if it is black.
PassToken(i) ==
    /\ i # Initiator
    /\ ~ active[i]
    /\ HoldsToken(i)
    /\ LET tok == Head(inbox[i]) IN
         inbox' = [inbox EXCEPT
                     ![i-1] = Append(@, [type  |-> "tok",
                                         q     |-> tok.q + counter[i],
                                         color |-> IF color[i] = "black"
                                                   THEN "black"
                                                   ELSE tok.color]),
                     ![i]   = Tail(@)]
    /\ color' = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED <<active, counter>>

(* Environment / computation actions *)

\* An active process sends a payload to some other process (bounded channel).
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Node \ {i} :
         /\ PlCount(inbox[j]) < MaxChan
         /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl"])]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, color>>

\* A process receives the payload at the head of its FIFO inbox.
\* Receipt activates it and turns it black.
RecvMsg(i) ==
    /\ inbox[i] # <<>>
    /\ Head(inbox[i]).type = "pl"
    /\ inbox'   = [inbox   EXCEPT ![i] = Tail(@)]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ active'  = [active  EXCEPT ![i] = TRUE]
    /\ color'   = [color   EXCEPT ![i] = "black"]

\* An active process spontaneously becomes passive.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, counter, inbox>>

-----------------------------------------------------------------------------
System == InitiateProbe \/ \E i \in Node \ {Initiator} : PassToken(i)

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Fairness ==
    /\ WF_vars(InitiateProbe)
    /\ \A i \in Node \ {Initiator} : WF_vars(PassToken(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Optional state constraint to keep TLC's state space finite.
StateConstraint ==
    \A i \in Node : counter[i] \in -(N * MaxChan) .. (N * MaxChan)

-----------------------------------------------------------------------------
(* Correctness properties *)

Quiescent ==
    \A i \in Node : ~ active[i] /\ PlCount(inbox[i]) = 0

\* The initiator holds a white token. Itself white and passive, it finds
\* that the token's counter plus its own contribution is zero.
TerminationDetected ==
    /\ HoldsToken(Initiator)
    /\ Head(inbox[Initiator]).color = "white"
    /\ Head(inbox[Initiator]).q + counter[Initiator] = 0
    /\ color[Initiator] = "white"
    /\ ~ active[Initiator]

\* Safety: the token is unique. Exactly one token exists, so at most one.
TokenUnique == NumTokens = 1
AtMostOneToken == NumTokens <= 1

\* Soundness: detection implies true quiescence.
Soundness == TerminationDetected => Quiescent

\* Bounded channels: every payload buffer respects its bound.
ChannelBound == \A i \in Node : PlCount(inbox[i]) <= MaxChan

\* The local counters exactly account for the payloads in transit.
CounterInv == SumSet(counter, Node) = InTransit

\* Safra's invariant. It gives the meaning of counters and colors relative
\* to the current token position. Visited processes are TokenPos+1 .. N-1.
SafraInv ==
    LET tp  == TokenPos
        tok == TheToken
    IN  \/ /\ \A i \in Rng(tp + 1, N - 1) : ~ active[i]
           /\ tok.q = SumSet(counter, Rng(tp + 1, N - 1))
        \/ SumSet(counter, Rng(0, tp)) + tok.q > 0
        \/ \E i \in Rng(0, tp) : color[i] = "black"
        \/ tok.color = "black"

Invariants ==
    /\ TypeOK
    /\ TokenUnique
    /\ AtMostOneToken
    /\ ChannelBound
    /\ CounterInv
    /\ SafraInv
    /\ Soundness

\* Quiescence is stable: once reached, it persists.
QuiescenceStable == [][Quiescent => Quiescent']_vars

\* Liveness: quiescence eventually leads to detection by the initiator.
Liveness == Quiescent ~> TerminationDetected

THEOREM Spec => []Invariants
THEOREM Spec => Liveness
=============================================================================