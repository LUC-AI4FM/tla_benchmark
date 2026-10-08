```tla
MODULE OneVariableSystem

EXTENDS Naturals, TLC

CONSTANTS InitState

VARIABLES x

Init == x = 0

Next == \/ /\ x = 0
              /\ x' \in {1, 2}
          \/ /\ x /= 0
              /\ x' = 0

Spec == SpecFairness /\ []Next_x

SpecFairness == WF_x(Next)

StabilizeAwayFromOneOrTwo == <>[]~(x \in {1, 2})

RepeatedReturnToZero == <>([]<>x = 0)

TemporalPropertyNegation == ~<>([]<>(x = 1))

PostCondition(trace) == 
    /\ trace \subseteq (INSTANCE Naturals!Nat => [pc: STRING, x: Nat])
    /\ \A i \in Indices(trace): 
        \/ i = 1
           /\ trace[i].pc = "Init"
           /\ trace[i].x = InitState
        \/ i > 1
           /\ trace[i].pc = "Next"
           /\ Let pcPrev == trace[i-1].pc;
                xPrev == trace[i-1].x;
                xCurrent == trace[i].x; 
             In /\ pcPrev = "Init" \/ pcPrev = "Next"
                /\ (/\ xPrev = 0
                    /\ xCurrent \in {1, 2}
                   \/ xPrev /= 0
                      /\ xCurrent = 0)

THEOREM Spec => []Init /\ StabilizeAwayFromOneOrTwo /\ RepeatedReturnToZero /\ TemporalPropertyNegation

```