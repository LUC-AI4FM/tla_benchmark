----------------------------- MODULE DigitMachine -----------------------------
EXTENDS Integers

CONSTANTS Max
ASSUME Max = 9

VARIABLES d

Even(n) == n % 2 = 0
Allowed(n) == n \in 0..Max /\ Even(n)

Init == d = 0

Next == Allowed(d')

Spec == Init /\ [][Next]_d

Inv == Allowed(d)
Safety == []Inv

StutterClosure == [](UNCHANGED d => Allowed(d'))
===============================================================================