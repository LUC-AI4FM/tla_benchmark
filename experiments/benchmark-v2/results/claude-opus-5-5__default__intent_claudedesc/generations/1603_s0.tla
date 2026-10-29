---- MODULE ModuleInstantiation ----
EXTENDS Naturals, TLC

---- MODULE Adder ----
EXTENDS Naturals
CONSTANTS a, b
Sum == a + b
====