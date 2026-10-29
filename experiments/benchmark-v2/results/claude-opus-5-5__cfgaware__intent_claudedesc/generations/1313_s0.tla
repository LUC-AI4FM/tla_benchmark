---------------------------- MODULE DieHard ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

(* Register 1 accumulates total gallons drawn from the fountain        *)
(* across all explored transitions (instrumentation).                  *)
ASSUME TLCSet(1, 0)

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ small = 0
        /\ big   = 0

FillSmall  == /\ small' = 3
              /\ big'   = big
              /\ TLCSet(1, TLCGet(1) + (3 - small))

FillBig    == /\ big'   = 5
              /\ small' = small
              /\ TLCSet(1, TLCGet(1) + (5 - big))

EmptySmall == /\ small' = 0
              /\ big'   = big

EmptyBig   == /\ big'   = 0
              /\ small' = small

SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3)
              /\ big'   = big - (small' - small)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* Predicate: the big jug contains exactly four gallons.               *)
HasFour == big = 4

(* Action predicate: a transition that changes both jugs at once.      *)
PourAction == /\ small' # small
              /\ big'   # big

-------------------------------------------------------------------------
(* Static model of the reachable state graph, used to cross-check       *)
(* the counts that TLC reports.                                         *)
St(s, b) == [small |-> s, big |-> b]

Succ(st) ==
  LET s == st.small
      b == st.big
      nb1 == Min(b + s, 5)
      ns2 == Min(b + s, 3)
  IN { St(3, b), St(s, 5), St(0, b), St(s, 0),
       St(s - (nb1 - b), nb1),
       St(ns2, b - (ns2 - s)) }

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  LET T == S \cup UNION { Succ(st) : st \in S }
  IN  IF T = S THEN S ELSE ReachFrom(T)

Reach == ReachFrom({ St(0, 0) })

FourStates == { st \in Reach : st.big = 4 }

BothChangeTransitions ==
  { <<st, t>> \in Reach \X Reach :
      /\ t \in Succ(st)
      /\ t.small # st.small
      /\ t.big   # st.big }

PossibleCounts ==
  [ hasFour    |-> Cardinality(FourStates),
    bothChange |-> Cardinality(BothChangeTransitions),
    drawn      |-> TLCGet(1) ]

(* Reachability / state-space-shape postcondition.                      *)
_POSSIBLE ==
  /\ FourStates # {}
  /\ Cardinality(Reach) = 16
  /\ TLCGet("stats").distinct  = 16
  /\ TLCGet("stats").generated = 97
  /\ TLCGet("stats").diameter  = 8
  /\ PrintT(PossibleCounts)
=========================================================================