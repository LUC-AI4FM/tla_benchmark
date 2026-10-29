---------------------------- MODULE PlusCalInstanceComma ----------------------------
EXTENDS Naturals, Sequences, TLC

---------------------------- MODULE InnerMod ----------------------------
EXTENDS Naturals
CONSTANTS a, b
Sum == a + b
=============================================================================