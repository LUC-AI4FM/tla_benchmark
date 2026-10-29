---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLE can

vars == <<can>>

BeanCount == can.black + can.white

TypeOK ==
    /\ can \in [black : Nat, white : Nat]
    /\ can.black >= 0
    /\ can.white >= 0

NonNegative == can.black >= 0 /\ can.white >= 0

Init ==
    /\ can \in {c \in [black : 0..MaxBeanCount, white : 0..MaxBeanCount] :
                    /\ c.black + c.white >= 1
                    /\ c.black + c.white <= MaxBeanCount}

PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED vars

Next ==
    \/ PickSameColorBlack
    \/ PickSameColorWhite
    \/ PickDifferentColor
    \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety invariants

BeanCountBounded == BeanCount >= 1 /\ BeanCount <= MaxBeanCount

\* Conservation property: the parity of the white bean count never changes.
WhiteParityConserved ==
    \A p \in {0, 1} :
        (can.white % 2 = p) => [](can.white % 2 = p)

\* Progress: every non-stuttering step removes exactly one bean.
StepDecreasesByOne ==
    [][BeanCount' = BeanCount - 1]_vars

\* Each step either decreases the count by one or the process has terminated.
ProgressAction ==
    [][(BeanCount > 1) => (BeanCount' = BeanCount - 1)]_vars

-----------------------------------------------------------------------------
\* Liveness properties

EventuallyOneBean == <>(BeanCount = 1)

TerminatesWithOneBean == <>[](BeanCount = 1)

\* Deterministic outcome: the final bean color is determined by the
\* initial parity of the white bean count.
FinalBeanColorDetermined ==
    \A w \in 0..MaxBeanCount :
        (can.white = w) =>
            [](BeanCount = 1 =>
                IF w % 2 = 1
                    THEN can.white = 1 /\ can.black = 0
                    ELSE can.black = 1 /\ can.white = 0)

LoopInvariant ==
    \A w \in 0..MaxBeanCount :
        (can.white = w) =>
            [](/\ can.white % 2 = w % 2
               /\ (BeanCount = 1 =>
                     (IF w % 2 = 1 THEN can.white = 1 ELSE can.black = 1)))

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []NonNegative
THEOREM Spec => []BeanCountBounded
THEOREM Spec => WhiteParityConserved
THEOREM Spec => StepDecreasesByOne
THEOREM Spec => EventuallyOneBean
THEOREM Spec => TerminatesWithOneBean
THEOREM Spec => FinalBeanColorDetermined
=============================================================================