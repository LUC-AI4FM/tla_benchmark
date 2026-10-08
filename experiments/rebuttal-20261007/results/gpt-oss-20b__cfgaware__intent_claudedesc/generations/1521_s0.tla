MODULE CoffeeCan
EXTENDS Naturals

CONSTANTS MaxBeans, InitBlack, InitWhite

VARIABLE b, w

vars == <<b, w>>

Total(b,w) == b + w

Init ==
    /\ 0 <= InitBlack
    /\ 0 <= InitWhite
    /\ InitBlack + InitWhite <= MaxBeans
    /\ b = InitBlack
    /\ w = InitWhite

BothBlack ==
    /\ b >= 2
    /\ b' = b - 1
    /\ w' = w

BothWhite ==
    /\ w >= 2
    /\ b' = b + 1
    /\ w' = w - 2

Mixed ==
    /\ b >= 1
    /\ w >= 1
    /\ b' = b - 1
    /\ w' = w

Next == BothBlack \/ BothWhite \/ Mixed

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Decrease ==
    [] ((b + w) > (b' + w'))

ParityInvariant ==
    [] ((w % 2) = (w' % 2))

Termination ==
    [] <> (Total(b,w) = 1)

FinalColor ==
    [] ((Total(b,w)=1) =>
        IF InitWhite % 2 = 0 THEN b=1 ELSE w=1)

THEOREM DecreaseProp == Spec => Decrease

THEOREM ParityInvariantProp == Spec => ParityInvariant

THEOREM TerminationProp == Spec => Termination

THEOREM FinalColorProp == Spec => FinalColor

END MODULE