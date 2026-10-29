--------------------------- MODULE MC_Session11afair ---------------------------
(***************************************************************************)
(* Model-checking wrapper around Session11afair.  It supplies a concrete   *)
(* data set and adds state and temporal properties over the inherited      *)
(* variables AVar and BVar.  The constant Data, the variables AVar and     *)
(* BVar, and the behavior specification Spec all come from Session11afair. *)
(***************************************************************************)
EXTENDS Session11afair

\* Concrete value set substituted for the constant Data in the configuration
ConstData == {"d1", "d2", "d3"}

\* Type correctness: each of AVar and BVar is a pair <<datum, bit>>
ABSpec_TypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}

\* If the bits of AVar and BVar are equal, the whole messages are equal
ABSpec_Inv ==
    (AVar[2] = BVar[2]) => (AVar = BVar)

\* AVar's bit alternates between 0 and 1 infinitely often
InfinitelyAlternating ==
    /\ []<>(AVar[2] = 0)
    /\ []<>(AVar[2] = 1)

\* AVar and BVar agree infinitely often, and they alternate forever
Liveness ==
    /\ []<>(AVar = BVar)
    /\ InfinitelyAlternating
=============================================================================