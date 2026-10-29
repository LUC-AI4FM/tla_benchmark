---- MODULE ModuleInstantiation ----
EXTENDS Naturals, TLC

---- MODULE Adder ----
EXTENDS Naturals
CONSTANTS A, B
Sum == A + B
====