```tla
oL[self]].R = lhR_oL[self]
       THEN /\ Assert(/\ mem[lh_oL[self]].V \in Val
                      /\ valBag[mem[lh_oL[self]].V] > 0,
                      "Failure of assertion: popLeft value not in valBag")
            /\ LeftHat' = lhR_oL[self]
            /\ mem' = [mem EXCEPT ![lh_oL[self]].R = lh_oL[self]]
            /\ result_oL' = [result_oL EXCEPT ![self] = mem[lh_oL[self]].V]
            /\ valBag' = [valBag EXCEPT ![mem[lh_oL[self]].V] = @ - 1]
            /\ pc' = [pc EXCEPT ![self] = "oL7"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "oL1"]
            /\ UNCHANGED << LeftHat, mem, result_oL, valBag >>
  /\ UNCHANGED << freeList, RightHat, rVal, stack, lh_oL, rh_oL, lhR_oL,
                  pLvars, pRvars, oRvars >>

oL7(self) ==
  /\ pc[self] = "oL7"
  /\ mem' = [mem EXCEPT ![lh_oL[self]].L = Dummy]
  /\ rVal' = [rVal EXCEPT ![self] = result_oL[self]]
  /\ Return(self)
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag,
                  pLvars, pRvars, oLvars, oRvars >>

popLeft(self) == oL1(self) \/ oL2(self) \/ oL3(self) \/ oL4(self)
                   \/ oL5(self) \/ oL6(self) \/ oL7(self)

-----------------------------------------------------------------------------
(*************************** procedure popRight ****************************)

oR1(self) ==
  /\ pc[self] = "oR1"
  /\ rh_oR' = [rh_oR EXCEPT ![self] = RightHat]
  /\ pc' = [pc EXCEPT ![self] = "oR2"]
  /\ UNCHANGED << shared, rVal, stack, lh_oR, rhL_oR, result_oR,
                  pLvars, pRvars, oLvars >>

oR2(self) ==
  /\ pc[self] = "oR2"
  /\ lh_oR' = [lh_oR EXCEPT ![self] = LeftHat]
  /\ pc' = [pc EXCEPT ![self] = "oR3"]
  /\ UNCHANGED << shared, rVal, stack, rh_oR, rhL_oR, result_oR,
                  pLvars, pRvars, oLvars >>

oR3(self) ==
  /\ pc[self] = "oR3"
  /\ IF mem[rh_oR[self]].R = rh_oR[self]
       THEN /\ rVal' = [rVal EXCEPT ![self] = "empty"]
            /\ Return(self)
       ELSE /\ IF rh_oR[self] = lh_oR[self]
                 THEN pc' = [pc EXCEPT ![self] = "oR4"]
                 ELSE pc' = [pc EXCEPT ![self] = "oR5"]
            /\ UNCHANGED << rVal, stack >>
  /\ UNCHANGED << shared, pLvars, pRvars, oLvars, oRvars >>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
oR4(self) ==
  /\ pc[self] = "oR4"
  /\ IF RightHat = rh_oR[self] /\ LeftHat = lh_oR[self]
       THEN /\ Assert(/\ mem[rh_oR[self]].V \in Val
                      /\ valBag[mem[rh_oR[self]].V] > 0,
                      "Failure of assertion: popRight value not in valBag")
            /\ RightHat' = Dummy
            /\ LeftHat' = Dummy
            /\ result_oR' = [result_oR EXCEPT ![self] = mem[rh_oR[self]].V]
            /\ valBag' = [valBag EXCEPT ![mem[rh_oR[self]].V] = @ - 1]
            /\ rVal' = [rVal EXCEPT ![self] = mem[rh_oR[self]].V]
            /\ Return(self)
       ELSE /\ pc' = [pc EXCEPT ![self] = "oR1"]
            /\ UNCHANGED << LeftHat, RightHat, result_oR, valBag, rVal, stack >>
  /\ UNCHANGED << mem, freeList, rh_oR, lh_oR, rhL_oR,
                  pLvars, pRvars, oLvars >>

oR5(self) ==
  /\ pc[self] = "oR5"
  /\ rhL_oR' = [rhL_oR EXCEPT ![self] = mem[rh_oR[self]].L]
  /\ pc' = [pc EXCEPT ![self] = "oR6"]
  /\ UNCHANGED << shared, rVal, stack, rh_oR, lh_oR, result_oR,
                  pLvars, pRvars, oLvars >>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
oR6(self) ==
  /\ pc[self] = "oR6"
  /\ IF RightHat = rh_oR[self] /\ mem[rh_oR[self]].L = rhL_oR[self]
       THEN /\ Assert(/\ mem[rh_oR[self]].V \in Val
                      /\ valBag[mem[rh_oR[self]].V] > 0,
                      "Failure of assertion: popRight value not in valBag")
            /\ RightHat' = rhL_oR[self]
            /\ mem' = [mem EXCEPT ![rh_oR[self]].L = rh_oR[self]]
            /\ result_oR' = [result_oR EXCEPT ![self] = mem[rh_oR[self]].V]
            /\ valBag' = [valBag EXCEPT ![mem[rh_oR[self]].V] = @ - 1]
            /\ pc' = [pc EXCEPT ![self] = "oR7"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "oR1"]
            /\ UNCHANGED << RightHat, mem, result_oR, valBag >>
  /\ UNCHANGED << freeList, LeftHat, rVal, stack, rh_oR, lh_oR, rhL_oR,
                  pLvars, pRvars, oLvars >>

oR7(self) ==
  /\ pc[self] = "oR7"
  /\ mem' = [mem EXCEPT ![rh_oR[self]].R = Dummy]
  /\ rVal' = [rVal EXCEPT ![self] = result_oR[self]]
  /\ Return(self)
  /\ UNCHANGED << freeList, LeftHat, RightHat, valBag,
                  pLvars, pRvars, oLvars, oRvars >>

popRight(self) == oR1(self) \/ oR2(self) \/ oR3(self) \/ oR4(self)
                    \/ oR5(self) \/ oR6(self) \/ oR7(self)

-----------------------------------------------------------------------------
(***************************** process Test ********************************)

T1(self) ==
  /\ pc[self] = "T1"
  /\ \/ /\ \E v \in Val : v_pL' = [v_pL EXCEPT ![self] = v]
        /\ stack' = [stack EXCEPT ![self] =
                       << [procedure |-> "pushLeft", pc |-> "T1"] >>
                       \o stack[self]]
        /\ pc' = [pc EXCEPT ![self] = "pL1"]
        /\ UNCHANGED v_pR
     \/ /\ \E v \in Val : v_pR' = [v_pR EXCEPT ![self] = v]
        /\ stack' = [stack EXCEPT ![self] =
                       << [procedure |-> "pushRight", pc |-> "T1"] >>
                       \o stack[self]]
        /\ pc' = [pc EXCEPT ![self] = "pR1"]
        /\ UNCHANGED v_pL
     \/ /\ stack' = [stack EXCEPT ![self] =
                       << [procedure |-> "popLeft", pc |-> "T1"] >>
                       \o stack[self]]
        /\ pc' = [pc EXCEPT ![self] = "oL1"]
        /\ UNCHANGED << v_pL, v_pR >>
     \/ /\ stack' = [stack EXCEPT ![self] =
                       << [procedure |-> "popRight", pc |-> "T1"] >>
                       \o stack[self]]
        /\ pc' = [pc EXCEPT ![self] = "oR1"]
        /\ UNCHANGED << v_pL, v_pR >>
  /\ UNCHANGED << shared, rVal, nd_pL, lh_pL, lhL_pL, rh_pL,
                  nd_pR, rh_pR, rhR_pR, lh_pR, oLvars, oRvars >>

test(self) == T1(self)

-----------------------------------------------------------------------------
Next == \E self \in Procs :
          \/ test(self)
          \/ pushLeft(self) \/ pushRight(self)
          \/ popLeft(self)  \/ popRight(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs :
             /\ WF_vars(test(self))
             /\ WF_vars(pushLeft(self))
             /\ WF_vars(pushRight(self))
             /\ WF_vars(popLeft(self))
             /\ WF_vars(popRight(self))

-----------------------------------------------------------------------------
(******************************* Properties ********************************)

TypeOK ==
  /\ mem \in [Address -> Node]
  /\ freeList \subseteq Address
  /\ LeftHat \in Address
  /\ RightHat \in Address
  /\ valBag \in [Val -> Nat]
  /\ rVal \in [Procs -> Val \cup {null, "okay", "full", "empty"}]

\* Every test process returns to control location T1 infinitely often.
Liveness == \A p \in Procs : []<>(pc[p] = "T1")

THEOREM Spec => []TypeOK
THEOREM Spec => Liveness
=============================================================================
```