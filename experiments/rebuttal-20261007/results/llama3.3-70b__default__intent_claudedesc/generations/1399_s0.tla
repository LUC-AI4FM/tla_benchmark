```
MODULE Toggle
EXTENDS Integers

CONSTANTS None

VARIABLES toggle

Init == (toggle = TRUE)

Next == (toggle' = ~toggle)

Spec == Init /\ [][Next]_toggle

AlwaysTrue == []<<toggle>>_toggle
AlwaysFalse == [](TRUE)
ExposeToggle == <<toggle>>_toggle

THEOREM Spec => []~(toggle = TRUE)
THEOREM Spec => AlwaysFalse
THEOREM Spec => [](toggle = toggle)
```
Note: The above TLA+ specification uses the `[]` operator to denote "always" (i.e., a property that holds at every step), and the `<>` operator is not used directly as it's typically used for stuttering closure in conjunction with other operators. Instead, properties are defined using the `[]` operator where applicable. The `THEOREM` statements are used to assert properties against the specification.