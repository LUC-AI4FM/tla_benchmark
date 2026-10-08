---------------------------- MODULE CounterSystem ----------------------------
EXTENDS Integers

CONSTANT MaxValue

VARIABLE counter

Init == (counter = 0)

SubcomponentIncrement == (counter < MaxValue) ∧ (counter' = counter + 1)
MainControllerStutter == (counter' = counter)

Next == (∃ x ∈ {SubcomponentIncrement, MainControllerStutter} : x)
       ∨ (¬∃ x ∈ {SubcomponentIncrement} : x)

Spec == Init ∧ [][Next]_counter
      ∧ WF_vars(<<SubcomponentIncrement>>_counter)

Prop == <>[]counter = MaxValue

THEOREM Spec => Prop

=============================================================================