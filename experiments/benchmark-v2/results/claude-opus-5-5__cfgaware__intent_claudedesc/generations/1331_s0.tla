------------------------------- MODULE EWD998Chan -------------------------------
(***************************************************************************)
(* Safra's termination detection algorithm (EWD998) on a ring of N nodes,  *)
(* where the message channels are modeled explicitly as sequences.        *)
(* Each node i has an inbox inbox[i] that holds both payload messages     *)
(* ("pl") and the single token ("tok").  The refinement mapping to the    *)
(* abstract EWD998 specification is given by the operators token and      *)
(* pending.  The abstract specification is inlined here so that the       *)
(* module is self-contained.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES
  active,   \* activation status of nodes
  color,    \* color of nodes
  counter,  \* nb of sent messages - nb of rcvd messages per node
  inbox     \* channels (sequences of messages) of each node

vars == <<active, color, counter, inbox>>

-----------------------------------------------------------------------------
(* Helper operators *)

\* Remove the i-th element of sequence s.
RemoveAt(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

\* Sum of f[x] for x in the finite set S.
RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  f[x] + SumSet(f, S \ {x})

-----------------------------------------------------------------------------

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message  == TokenMsg \cup BasicMsg

TypeOK ==
  /\ counter \in [Node -> Int]
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ inbox \in [Node -> Seq(Message)]
  \* There is exactly one token in the whole ring.
  /\ \E i \in Node : \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"
  /\ \A i, j \in Node :
       \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
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

PassToken(i) ==
  /\ ~ active[i]
  /\ \E j \in 1 .. Len(inbox[i]) :
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

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

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
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract EWD998 specification.               *)

token ==
  LET tpos == CHOOSE i \in Node :
                \E j \in 1 .. Len(inbox[i]) : inbox[i][j].type = "tok"
      tidx == CHOOSE j \in 1 .. Len(inbox[tpos]) : inbox[tpos][j].type = "tok"
  IN  [pos   |-> tpos,
       q     |-> inbox[tpos][tidx].q,
       color |-> inbox[tpos][tidx].color]

pending ==
  [i \in Node |-> Len(SelectSeq(inbox[i], LAMBDA m : m.type = "pl"))]

-----------------------------------------------------------------------------
(* Abstract EWD998 specification (expressed over the mapped variables).   *)

absvars == <<active, color, counter, pending, token>>

AInit ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter = [i \in Node |-> 0]
  /\ pending = [i \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

AInitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

APassToken(i) ==
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [pos   |-> i - 1,
               q     |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

ASendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

ARecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  /\ color' = [color EXCEPT ![i] = "black"]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED token

ADeactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

ASystem == AInitiateProbe \/ \E i \in Node \ {0} : APassToken(i)
AEnvironment == \E i \in Node : ASendMsg(i) \/ ARecvMsg(i) \/ ADeactivate(i)
ANext == ASystem \/ AEnvironment

EWD998Spec == AInit /\ [][ANext]_absvars

\* Refinement theorem (checked as a PROPERTY): Spec => EWD998Spec
THEOREM Refinement == Spec => EWD998Spec

-----------------------------------------------------------------------------
(* Safety: the inductive invariant of EWD998 and termination detection.   *)

Sum(f, lo, hi) == SumSet(f, {k \in Node : lo <= k /\ k <= hi})

Termination ==
  /\ \A i \in Node : ~ active[i]
  /\ \A i \in Node : pending[i] = 0

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection == terminationDetected => Termination

AbsInv ==
  /\ Sum(counter, 0, N-1) = Sum(pending, 0, N-1)
  /\ \/ /\ \A i \in Node : i > token.pos => ~ active[i]
        /\ token.q = Sum(counter, token.pos + 1, N-1)
     \/ Sum(counter, 0, token.pos) + token.q > 0
     \/ \E i \in Node : i <= token.pos /\ color[i] = "black"
     \/ token.color = "black"

EWD998Inv ==
  /\ AbsInv
  /\ TerminationDetection

\* Liveness: once terminated, termination is eventually detected.
Liveness == Termination ~> terminationDetected

-----------------------------------------------------------------------------
(* Model-checking helpers.                                                 *)

StateConstraint ==
  \A i \in Node :
    /\ counter[i] <= 3
    /\ counter[i] >= -3
    /\ Len(inbox[i]) <= 3

ActionConstraint ==
  \A i \in Node : Len(inbox'[i]) <= Len(inbox[i]) + 1

\* Stop exploring once termination has been detected.
Stop == ~ terminationDetected

PostCondition ==
  TLCGet("stats").diameter >= 1

=============================================================================