---------------------------- MODULE CounterExample ----------------------------
EXTENDS Integers

CONSTANT MaxValue

VARIABLE counter

InnerModule == INSTANCE Inner WITH counter <- counter
Spec == /\ counter = 0
        /\ [][Next]_counter
        /\ WF_vars(InnerModule!Step)

Prop == <>[](counter = MaxValue)

Next == InnerModule!Next

WF_vars(Step) == InnerModule!WF_vars(InnerStep)

==================================