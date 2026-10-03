MODULE CoffeeCan

IMPORTS Naturals, Temporal

CONSTANT MaxBeans, InitBlack, InitWhite

VARIABLE state

(* Record type for the bean counts *)
State == [black : Nat, white : Nat]

Init ==
    /\ state = [black |-> InitBlack, white |-> InitWhite]
    /\ 0 <= InitBlack
    /\ 0 <= InitWhite
    /\ InitBlack + InitWhite <= MaxBeans

TypeInvariant ==
    /\ 0 <= state.black
    /\ 0 <= state.white
    /\ state.black + state.white <= MaxBeans

RemoveBB ==
    /\ state.black >= 2
    /\ state' = [state EXCEPT !.black = state.black - 2,
                                 !.white = state.white + 1]

RemoveWW ==
    /\ state.white >= 2
    /\ state' = [state EXCEPT !.black = state.black + 1,
                                 !.white = state.white - 2]

RemoveBW ==
    /\ state.black >= 1
    /\ state.white >= 1
    /\ state' = [state EXCEPT !.black = state.black - 1]   (* white unchanged *)

Stutter ==
    /\ state.black + state.white = 1
    /\ state' = state

Next == RemoveBB \/ RemoveWW \/ RemoveBW \/ Stutter

TotalDecrease ==
    (Next /\ ~Stutter) => (state'.black + state'.white) < (state.black + state.white)

ParityInvariant ==
    (state.white % 2) = (InitWhite % 2)

Termination ==
    [] (WF_vars(Next) => <> (state.black + state.white = 1))

FinalColorHypothesis ==
    [] ((InitWhite % 2 = 0) => <> (state.black = 1 /\ state.white = 0)) /\
    [] ((InitWhite % 2 = 1) => <> (state.black = 0 /\ state.white = 1))

Spec == Init /\ [][Next]_state

THEOREM TypeInvariantIsMaintained
    ASSUME Spec
    PROVE [] TypeInvariant

THEOREM TotalBeansDecrease
    ASSUME Spec
    PROVE [] TotalDecrease

THEOREM ParityLoopInvariant
    ASSUME Spec
    PROVE [] ParityInvariant

THEOREM TerminationUnderFairness
    ASSUME Spec
    PROVE Termination

THEOREM FinalColorHypothesisTheorem
    ASSUME Spec
    PROVE FinalColorHypothesis

END MODULE