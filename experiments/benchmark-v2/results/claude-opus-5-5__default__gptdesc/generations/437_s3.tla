---------------------------- MODULE PrefixPostfixOps ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Higher-order operators that take a unary operator as an argument.       *)
(***************************************************************************)
Pre(F(_), a)  == F(a)
Post(G(_), a) == G(a)
Twice(F(_), a) == F(F(a))

(***************************************************************************)
(* User-defined prefix and postfix operators.                              *)
(***************************************************************************)
-. a == {a}
a ^+ == a \cup {0}
a ^* == a \cup {1}
a ^# == a \cup {2}

(***************************************************************************)
(* Syntactic uses of built-in prefix / postfix operators as arguments.     *)
(***************************************************************************)
PowerSet(S)   == Pre(SUBSET, S)
BigUnion(S)   == Pre(UNION, S)
Dom(f)        == Pre(DOMAIN, f)
Neg(a)        == Pre(-., a)
PlusOf(S)     == Post(^+, S)
StarOf(S)     == Post(^*, S)
HashOf(S)     == Post(^#, S)

(***************************************************************************)
(* A tiny two-variable state machine over sets.                            *)
(***************************************************************************)
Init == /\ x = {}
        /\ y = {1}

AddElem == /\ x = {}
           /\ x' = {1}
           /\ Pre(UNCHANGED, y)

ClearElem == /\ x # {}
             /\ x' = {}
             /\ Post(', y) = y

Next == AddElem \/ ClearElem

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Action / state-level uses of ENABLED, UNCHANGED and prime as arguments. *)
(***************************************************************************)
CanStep      == Pre(ENABLED, Next)
YUnchanged   == Pre(UNCHANGED, y)
PrimedX      == Post(', x)

(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
TypeOK == /\ x \in SUBSET {1}
          /\ y = {1}

AlwaysEnabled == CanStep

(***************************************************************************)
(* Derived temporal property built from [] and <> passed as arguments.     *)
(***************************************************************************)
Property == Pre([], Pre(<>, x = {1}))

EventuallyEmpty == Pre([], Pre(<>, x = {}))

Liveness == Property /\ EventuallyEmpty

THEOREM Spec => Pre([], TypeOK)
THEOREM Spec => Property

(***************************************************************************)
(* Assumptions validating parsing and evaluation of the operators.         *)
(***************************************************************************)
ASSUME
  /\ Print(<<"SUBSET", PowerSet({1})>>, TRUE)
  /\ PowerSet({1}) = {{}, {1}}
  /\ Print(<<"UNION", BigUnion({{1}, {2}})>>, TRUE)
  /\ BigUnion({{1}, {2}}) = {1, 2}
  /\ Print(<<"DOMAIN", Dom(<<5, 6>>)>>, TRUE)
  /\ Dom(<<5, 6>>) = {1, 2}
  /\ Print(<<"-.", Neg(3)>>, TRUE)
  /\ Neg(3) = {3}
  /\ Print(<<"^+", PlusOf({1})>>, TRUE)
  /\ PlusOf({1}) = {0, 1}
  /\ StarOf({2}) = {1, 2}
  /\ HashOf({1}) = {1, 2}
  /\ Twice(SUBSET, {}) = {{}, {{}}}
  /\ Twice(-., 1) = {{1}}
  /\ ({5})^+ = {0, 5}
  /\ -. 7 = {7}

=============================================================================