---------------------------- MODULE LetInstance ----------------------------
EXTENDS Naturals

VARIABLE x

vars == << x >>

---------------------------- MODULE Inner ----------------------------
EXTENDS Naturals

VARIABLE val

ValuePlusOne == val + 1
=======================================================================