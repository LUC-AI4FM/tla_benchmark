---------------------------- MODULE PrefixPostfixHigherOrder ----------------------------
(***************************************************************************)
(* Checks that a TLA+ tool handles prefix and postfix operators passed as  *)
(* arguments to higher-order operators. Each passed operator must behave   *)
(* exactly like the same operator applied directly.                        *)
(***************************************************************************)

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Higher-order operators that take a prefix or a postfix operator as an   *)
(* argument and apply it.                                                  *)
(***************************************************************************)
Pre(Op(_), a)  == Op(a)
Post(Op(_), a) == Op(a)

(***************************************************************************)
(* User-defined postfix operators, one for each postfix syntactic form.    *)
(***************************************************************************)
s ^+ == s \cup {"plus"}
s ^* == s \cup {"star"}
s ^# == s \cup {"hash"}

(***************************************************************************)
(* User-defined operator used in prefix position.                          *)
(***************************************************************************)
Neg(b) == ~b

(***************************************************************************)
(* Constant-level fixtures.                                                *)
(***************************************************************************)
S == {"a", "b"}
f == [e \in S |-> {e}]

(***************************************************************************)
(* Static equivalence checks, evaluated when the spec is initialized.      *)
(***************************************************************************)
ASSUME Pre(LAMBDA b : ~b, TRUE) = ~TRUE
ASSUME Pre(LAMBDA b : ~b, FALSE) = ~FALSE
ASSUME Pre(LAMBDA b : \lnot b, TRUE) = \lnot TRUE
ASSUME Pre(LAMBDA T : SUBSET T, S) = SUBSET S
ASSUME Pre(LAMBDA T : UNION T, {S, {"c"}}) = UNION {S, {"c"}}
ASSUME Pre(LAMBDA g : DOMAIN g, f) = DOMAIN f
ASSUME Pre(Neg, TRUE) = Neg(TRUE)
ASSUME Post(LAMBDA T : T^+, S) = S^+
ASSUME Post(LAMBDA T : T^*, S) = S^*
ASSUME Post(LAMBDA T : T^#, S) = S^#
ASSUME Post(LAMBDA T : T^+, S) = S \cup {"plus"}
ASSUME Post(LAMBDA T : T^*, S) = S \cup {"star"}
ASSUME Post(LAMBDA T : T^#, S) = S \cup {"hash"}

(***************************************************************************)
(* Minimal state machine with set-valued variables. It gives the temporal  *)
(* and action operators a behavior to be evaluated against.                *)
(***************************************************************************)
Init ==
    /\ x = {}
    /\ y = {}

AddX ==
    /\ x' = x \cup {"a"}
    /\ UNCHANGED y

AddY ==
    /\ y' = y \cup {"b"}
    /\ UNCHANGED x

Next == AddX \/ AddY

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* State predicates built from passed action operators. They must hold in  *)
(* every reachable state.                                                  *)
(***************************************************************************)
TypeOK ==
    /\ x \subseteq {"a"}
    /\ y \subseteq {"b"}

EnabledInv ==
    /\ Pre(LAMBDA A : ENABLED A, Next)
    /\ Pre(LAMBDA A : ENABLED A, Next) = ENABLED Next
    /\ Pre(LAMBDA A : ENABLED A, AddX) = ENABLED AddX
    /\ Pre(LAMBDA A : ENABLED A, AddY)

Inv == TypeOK /\ EnabledInv

(***************************************************************************)
(* Action properties built from passed UNCHANGED and prime operators.      *)
(* They must hold across every step of the specification.                  *)
(***************************************************************************)
ActProp ==
    /\ Post(LAMBDA e : e', x) = x \cup {"a"} \/ Post(LAMBDA e : e', x) = x
    /\ Post(LAMBDA e : e', y) = y \cup {"b"} \/ Post(LAMBDA e : e', y) = y
    /\ Post(LAMBDA e : e', x) = x'
    /\ Pre(LAMBDA v : UNCHANGED v, x) \/ Pre(LAMBDA v : UNCHANGED v, y)
    /\ Pre(LAMBDA v : UNCHANGED v, y) = UNCHANGED y
    /\ Pre(LAMBDA v : UNCHANGED v, x) = (x' = x)

(***************************************************************************)
(* Temporal property that uses the passed always and eventually operators. *)
(***************************************************************************)
Property ==
    /\ Pre(LAMBDA F : []F, Inv)
    /\ Pre(LAMBDA F : <>F, Init)
    /\ [][ActProp]_vars
    /\ [][Pre(LAMBDA v : UNCHANGED v, x) \/ Post(LAMBDA e : e', x) = x \cup {"a"}]_vars

=============================================================================