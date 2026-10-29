---------------------------- MODULE PlusCalInstanceWithComma ----------------------------
EXTENDS Naturals, Sequences, TLC

---------------------------- MODULE InnerDef ----------------------------
EXTENDS Naturals
CONSTANTS A, B
Sum == A + B
=========================================================================