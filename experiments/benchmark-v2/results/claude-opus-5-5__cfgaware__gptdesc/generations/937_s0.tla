---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

(***************************************************************************)
(* Definitions inherited from the HourClock specification.                 *)
(***************************************************************************)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness-augmented specification.                                       *)
(***************************************************************************)
LSpec == HC /\ WF_hr(HCnxt)

(***************************************************************************)
(* Temporal properties.                                                    *)
(***************************************************************************)
AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1..12 : []<>(hr = n)

TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

(***************************************************************************)
(* Postcondition: checking a settling property such as <>[](hr = 1)        *)
(* against LSpec yields a counterexample consisting of a lasso-shaped      *)
(* behavior: a finite prefix reaching some hour value, followed by a cycle *)
(* through all twelve hour values 1, 2, ..., 12, 1, ... that repeats       *)
(* forever, so hr never settles on any single value.                      *)
(***************************************************************************)
=============================================================================