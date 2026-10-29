--------------------------- MODULE DieHard ---------------------------
EXTENDS Naturals, TLC

(***************************************************************************)
(* TLC registers used for instrumentation:                                 *)
(*   1 : total gallons drawn from the fountain over all explored behaviors *)
(*   2 : number of distinct states satisfying big = 4                      *)
(*   3 : number of generated transitions changing both jugs at once        *)
(***************************************************************************)
GallonsReg  == 1
FourReg     == 2
BothReg     == 3

ASSUME /\ TLCSet(GallonsReg, 0)
       /\ TLCSet(FourReg, 0)
       /\ TLCSet(BothReg, 0)

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ small = 0
        /\ big   = 0

\* Records water drawn from the fountain.
Draw(n) == TLCSet(GallonsReg, TLCGet(GallonsReg) + n)

FillSmall == /\ small' = 3
             /\ big'   = big
             /\ Draw(3 - small)

FillBig == /\ big'   = 5
           /\ small' = small
           /\ Draw(5 - big)

EmptySmall == /\ small' = 0
              /\ big'   = big

EmptyBig == /\ big'   = 0
            /\ small' = small

SmallToBig == LET amt == Min(small, 5 - big)
              IN  /\ small' = small - amt
                  /\ big'   = big + amt

BigToSmall == LET amt == Min(big, 3 - small)
              IN  /\ big'   = big - amt
                  /\ small' = small + amt

\* Counts transitions in which both jugs change simultaneously.
CountBoth == TLCSet(BothReg,
                    IF small' # small /\ big' # big
                       THEN TLCGet(BothReg) + 1
                       ELSE TLCGet(BothReg))

Next == /\ \/ FillSmall
           \/ FillBig
           \/ EmptySmall
           \/ EmptyBig
           \/ SmallToBig
           \/ BigToSmall
        /\ CountBoth

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
BigIsFour == big = 4

\* Instrumentation invariant: evaluated once per distinct state; counts
\* states satisfying the "big jug contains four gallons" predicate.
CountFour == TLCSet(FourReg,
                    IF BigIsFour THEN TLCGet(FourReg) + 1
                                 ELSE TLCGet(FourReg))

\* Classic counterexample-style invariant (violating it shows a solution).
NotSolved == big # 4

(***************************************************************************)
(* Post-condition: checked by TLC after exhaustive exploration.            *)
(*   - big = 4 is reachable (2 such states: <<0,4>> and <<3,4>>)           *)
(*   - 16 distinct states, diameter 8, 97 generated states                 *)
(*   - 14 generated transitions change both jugs                           *)
(*   - 64 gallons drawn from the fountain across all explored fills        *)
(***************************************************************************)
PostCondition ==
    /\ TLCGet(FourReg) > 0
    /\ TLCGet(FourReg) = 2
    /\ TLCGet(BothReg) = 14
    /\ TLCGet(GallonsReg) = 64
    /\ TLCGet("stats").distinct  = 16
    /\ TLCGet("stats").diameter  = 8
    /\ TLCGet("stats").generated = 97

(***************************************************************************)
(* Suggested TLC configuration (single worker):                            *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeOK                                                      *)
(*   INVARIANT CountFour                                                   *)
(*   POSTCONDITION PostCondition                                           *)
(***************************************************************************)
=============================================================================