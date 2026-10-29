------------------------- MODULE PrefixPostfixHigherOrder -------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

Elems == {1, 2}

-----------------------------------------------------------------------------
(* User-defined prefix and postfix operators                              *)
-----------------------------------------------------------------------------

-. a == 0 - a

a ^+ == a + 1
a ^* == a * 2
a ^# == {a}

-----------------------------------------------------------------------------
(* Higher-order operators                                                 *)
-----------------------------------------------------------------------------

Apply(Op(_), a) == Op(a)

ApplyTwice(Op(_), a) == Op(Op(a))

Compose(F(_), G(_), a) == F(G(a))

-----------------------------------------------------------------------------
(* Static (constant-level) checks                                         *)
-----------------------------------------------------------------------------

TestFun == [i \in {1, 2, 3} |-> i * 10]

ASSUME Apply(~, FALSE) = ~FALSE
ASSUME Apply(~, TRUE) = ~TRUE
ASSUME Apply(\lnot, TRUE) = \lnot TRUE
ASSUME Apply(\neg, FALSE) = \neg FALSE
ASSUME ApplyTwice(~, TRUE) = TRUE

ASSUME Apply(SUBSET, {1, 2}) = SUBSET {1, 2}
ASSUME Apply(SUBSET, {}) = {{}}
ASSUME Apply(UNION, {{1}, {2, 3}}) = UNION {{1}, {2, 3}}
ASSUME Apply(UNION, {{1}, {2, 3}}) = {1, 2, 3}
ASSUME Apply(DOMAIN, TestFun) = DOMAIN TestFun
ASSUME Apply(DOMAIN, TestFun) = {1, 2, 3}
ASSUME Compose(UNION, SUBSET, {1, 2}) = UNION SUBSET {1, 2}

ASSUME Apply(-., 3) = -. 3
ASSUME Apply(-., 0) = 0
ASSUME Apply(^+, 3) = 3^+
ASSUME Apply(^+, 3) = 4
ASSUME Apply(^*, 3) = 3^*
ASSUME Apply(^*, 3) = 6
ASSUME Apply(^#, 3) = 3^#
ASSUME Apply(^#, 3) = {3}
ASSUME ApplyTwice(^+, 3) = (3^+)^+
ASSUME ApplyTwice(^*, 3) = 12
ASSUME Compose(^+, ^*, 3) = (3^*)^+
ASSUME Compose(^#, ^+, 3) = {4}

-----------------------------------------------------------------------------
(* Minimal state machine                                                  *)
-----------------------------------------------------------------------------

TypeOK == /\ x \subseteq Elems
          /\ y \subseteq Elems

Init == /\ x = {}
        /\ y = {}

AddX == \E e \in Elems : /\ x' = x \cup {e}
                         /\ UNCHANGED y

AddY == \E e \in Elems : /\ y' = y \cup {e}
                         /\ UNCHANGED x

Reset == /\ x' = {}
         /\ y' = {}

Next == AddX \/ AddY \/ Reset

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants built from passed action operators                          *)
-----------------------------------------------------------------------------

EnabledEquiv == Apply(ENABLED, Next) = ENABLED Next

EnabledHolds == Apply(ENABLED, Next)

EnabledAddX == Apply(ENABLED, AddX) = ENABLED AddX

SubsetStateEquiv == Apply(SUBSET, x) = SUBSET x

UnionStateEquiv == Apply(UNION, {x, y}) = x \cup y

Inv == /\ TypeOK
       /\ EnabledEquiv
       /\ EnabledHolds
       /\ EnabledAddX
       /\ SubsetStateEquiv
       /\ UnionStateEquiv

-----------------------------------------------------------------------------
(* Action properties built from passed action operators                   *)
-----------------------------------------------------------------------------

PrimeEquiv == Apply(', x) = x'

PrimeEquivY == Apply(', y) = y'

UnchangedEquiv == Apply(UNCHANGED, x) = UNCHANGED x

UnchangedVarsEquiv == Apply(UNCHANGED, vars) = UNCHANGED vars

PrimeStep == Apply(', x) \subseteq Elems /\ Apply(', y) \subseteq Elems

PrimeEquivProp == [][PrimeEquiv /\ PrimeEquivY]_vars

UnchangedEquivProp == [][UnchangedEquiv /\ UnchangedVarsEquiv]_vars

PrimeStepProp == [][PrimeStep]_vars

AddYKeepsX == [][AddY => Apply(UNCHANGED, x)]_vars

-----------------------------------------------------------------------------
(* Temporal properties using passed temporal operators                    *)
-----------------------------------------------------------------------------

AlwaysTypeOK == Apply([], TypeOK)

AlwaysEnabled == Apply([], Apply(ENABLED, Next))

EventuallyTrivial == Apply([], Apply(<>, TypeOK))

=============================================================================