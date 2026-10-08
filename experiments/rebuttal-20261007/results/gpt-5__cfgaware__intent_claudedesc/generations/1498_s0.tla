----------------------------- MODULE ToggleSystem -----------------------------

VARIABLE b

Not(x) == ~x

Init == b = FALSE

ActionA == b' = Not(b)
ActionB == b' = Not(b)

Next == ActionA \/ ActionB

=============================================================================