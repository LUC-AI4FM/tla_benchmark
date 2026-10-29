------------------------------- MODULE PrefixPostfixOps -------------------------------
(***************************************************************************)
(* Test specification: passing prefix and postfix operators as operator    *)
(* arguments, and defining custom prefix and postfix operators.            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Custom prefix and postfix operator definitions                          *)
(***************************************************************************)
-. S    == {} \ S              \* custom prefix minus: "negation" of a set
S ^+    == S \cup {0}          \* custom postfix ^+
S ^*    == SUBSET S            \* custom postfix ^*
S ^#    == Cardinality(S)      \* custom postfix ^#

(***************************************************************************)
(* Higher-order operators taking prefix / postfix operator parameters      *)
(***************************************************************************)
ApplyPre(-. _, a)   == -. a
ApplyPost(_ ^+, a)  == a ^+
ApplyPost2(_ ^#, a) == a ^#
Apply(Op(_), a)     == Op(a)
Twice(Op(_), a)     == Op(Op(a))

(***************************************************************************)
(* Built-in prefix / postfix operators supplied to higher-order operators  *)
(***************************************************************************)
BoxOf(F)        == Apply(LAMBDA e : []e, F)
DiamondOf(F)    == Apply(LAMBDA e : <>e, F)
EnabledOf(A)    == Apply(LAMBDA e : ENABLED e, A)
UnchangedOf(v)  == Apply(LAMBDA e : UNCHANGED e, v)
PrimeOf(v)      == Apply(LAMBDA e : e', v)
SubsetOf(S)     == Apply(LAMBDA e : SUBSET e, S)
UnionOf(S)      == Apply(LAMBDA e : UNION e, S)
DomainOf(f)     == Apply(LAMBDA e : DOMAIN e, f)

UsePrefix(S)    == ApplyPre(-., S)
UsePostfix(S)   == ApplyPost(^+, S)
UsePostfix2(S)  == ApplyPost2(^#, S)

(***************************************************************************)
(* Tiny two-variable state machine over sets                               *)
(***************************************************************************)
Init == /\ x = {}
        /\ y = {1}

Grow == /\ Cardinality(x) < 2
        /\ PrimeOf(x) = x \cup y
        /\ PrimeOf(y) = y \cup {Cardinality(y) + 1}

Stop == /\ Cardinality(x) >= 2
        /\ UnchangedOf(vars)

Next == Grow \/ Stop

Spec == Init /\ BoxOf([Next]_vars) /\ WF_vars(Grow)

(***************************************************************************)
(* Safety invariant and derived temporal property                          *)
(***************************************************************************)
TypeOK == /\ x \in SubsetOf(Nat)
          /\ y \in SubsetOf(Nat)

Inv == x \subseteq UnionOf({x, y})

Property == BoxOf(EnabledOf(Next)) /\ DiamondOf(BoxOf(UnchangedOf(vars) \/ ~EnabledOf(Grow)))

Live == <>(Cardinality(x) >= 2)

THEOREM Spec => [](TypeOK /\ Inv) /\ Live

(***************************************************************************)
(* Constant-level checks of parsing and evaluation                         *)
(***************************************************************************)
ASSUME
  /\ Print(<<"SUBSET", SubsetOf({1, 2})>>, TRUE)
  /\ SubsetOf({1, 2}) = {{}, {1}, {2}, {1, 2}}
  /\ Print(<<"UNION", UnionOf({{1}, {2, 3}})>>, TRUE)
  /\ UnionOf({{1}, {2, 3}}) = {1, 2, 3}
  /\ Print(<<"DOMAIN", DomainOf(<<"a", "b">>)>>, TRUE)
  /\ DomainOf(<<"a", "b">>) = {1, 2}
  /\ Print(<<"-.", UsePrefix({1})>>, TRUE)
  /\ UsePrefix({1}) = {}
  /\ -. {1, 2} = {}
  /\ Print(<<"^+", UsePostfix({1})>>, TRUE)
  /\ UsePostfix({1}) = {0, 1}
  /\ {5} ^+ = {0, 5}
  /\ Print(<<"^*", {1} ^*>>, TRUE)
  /\ {1} ^* = {{}, {1}}
  /\ Print(<<"^#", UsePostfix2({1, 2, 3})>>, TRUE)
  /\ UsePostfix2({1, 2, 3}) = 3
  /\ Twice(LAMBDA e : SUBSET e, {}) = {{}, {{}}}
  /\ Twice(LAMBDA e : e ^+, {7}) = {0, 7}
=======================================================================================