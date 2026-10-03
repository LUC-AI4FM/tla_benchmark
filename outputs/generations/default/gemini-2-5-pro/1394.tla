---- MODULE Github702 ----
EXTENDS Integers

VARIABLES y, z

fizzbuzz == "fizzbuzz"

xu == INSTANCE x_unchanged WITH x <- fizzbuzz

Init == xu!Init
Next == xu!Next
Spec == xu!Spec

=============================================================================