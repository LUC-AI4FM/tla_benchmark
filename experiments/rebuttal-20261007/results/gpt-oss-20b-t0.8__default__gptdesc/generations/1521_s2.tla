---- MODULE CoffeeCan ----
EXTENDS Naturals

CONSTANTS MaxBeans, InitBlack, InitWhite

VARIABLE state

(* Type invariant for the state variable *)
TypeInvariant ==
  /\ 0 <= state.black
  /\ 0 <= state.white
  /\ state.black + state.white <= MaxBeans

(* Initial condition *)
Init ==
  /\ state = [black -> InitBlack, white -> InitWhite]
  /\ TypeInvariant
  /\ (InitBlack + InitWhite) >= 1

(* Actions *)
RemoveTwoBlack ==
  /\ state.black >= 2
  /\ LET newState == [state EXCEPT !.black = state.black - 1] IN
     state' = newState

RemoveTwoWhite ==
  /\ state.white >= 2
  /\ LET newState == [state EXCEPT 
                        !.black = state.black + 1,
                        !.white = state.white - 2] IN
     state' = newState

RemoveOneOfEach ==
  /\ state.black >= 1
  /\ state.white >= 1
  /\ LET newState == [state EXCEPT !.black = state.black - 1] IN
     state' = newState

TermStutter ==
  /\ (state.black + state.white) = 1
  /\ state' = state

Next == RemoveTwoBlack \/ RemoveTwoWhite \/ RemoveOneOfEach \/ TermStutter

(* Safety invariants *)
TotalDecreaseInvariant ==
  (state.black + state.white) >= (state'.black + state'.white)

ParityInvariant ==
  (state.white MOD 2) = (InitWhite MOD 2)

(* Liveness property *)
TerminationLiveness == <> (state.black + state.white = 1)

(* Hypothesis relating initial white parity to final bean color *)
HypothesisFinalColor ==
  (state.black + state.white = 1) =>
    ((InitWhite MOD 2 = 0 /\ state.black = 1) \/ 
     (InitWhite MOD 2 = 1 /\ state.white = 1))

Spec == Init
        /\ [][Next]_state
        /\ WF(Next)
        /\ TerminationLiveness

THEOREM TypeInvTheorem ==
  [] TypeInvariant

THEOREM TotalDecreaseTheorem ==
  [] TotalDecreaseInvariant

THEOREM ParityInvariantTheorem ==
  [] ParityInvariant

THEOREM FinalColorHypothesis ==
  [] HypothesisFinalColor
---- END MODULE ----