---------------------------- MODULE PrefixPostfixOps ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

-----------------------------------------------------------------------------
(* Higher-order operators that take a unary operator as an argument.       *)
-----------------------------------------------------------------------------

Apply(Op(_), e) == Op(e)

ApplyTwice(Op(_), e) == Op(Op(e))

ApplyBoth(Op1(_), Op2(_), e) == Op1(e) /\ Op2(e)

-----------------------------------------------------------------------------
(* User-defined prefix and postfix operators.                              *)
-----------------------------------------------------------------------------

-. s == {}            \* custom prefix operator (unary minus symbol)

s ^+ == s \cup {s}    \* custom postfix operator: successor set
s ^* == SUBSET s      \* custom postfix operator: power set
s ^# == UNION s       \* custom postfix operator: union of elements

-----------------------------------------------------------------------------
(* Wrappers that expose built-in prefix and postfix operators so that      *)
(* they can be passed as operator arguments.                               *)
-----------------------------------------------------------------------------

BoxOp(F)       == []F
DiamondOp(F)   == <>F
EnabledOp(A)   == ENABLED A
UnchangedOp(e) == UNCHANGED e
SubsetOp(S)    == SUBSET S
UnionOp(S)     == UNION S
DomainOp(f)    == DOMAIN f
PrimeOp(e)     == e'

NegOp(S)       == -. S
SuccOp(S)      == S ^+
PowOp(S)       == S ^*
BigUOp(S)      == S ^#

-----------------------------------------------------------------------------
(* A tiny two-variable state machine over sets.                            *)
-----------------------------------------------------------------------------

TypeOK == /\ x \in SUBSET SUBSET {}
          /\ y \in SUBSET SUBSET {}

Init == /\ x = {}
        /\ y = {{}}

Swap == /\ Apply(PrimeOp, x) = y
        /\ Apply(PrimeOp, y) = x

Stay == Apply(UnchangedOp, vars)

Next == Swap \/ Stay

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Temporal property built by passing temporal/action operators as args.   *)
-----------------------------------------------------------------------------

Property ==
    /\ Apply(BoxOp, TypeOK)
    /\ Apply(BoxOp, Apply(EnabledOp, Next))
    /\ Apply(BoxOp, Apply(DiamondOp, x \cup y = {{}}) \/ TRUE)
    /\ Apply(BoxOp, Apply(UnionOp, x \cup y) = {})

-----------------------------------------------------------------------------
(* Constant-level checks of parsing and evaluation.                        *)
-----------------------------------------------------------------------------

ASSUME
    /\ Print("SUBSET as argument", TRUE)
    /\ Apply(SubsetOp, {1}) = {{}, {1}}
    /\ Print("UNION as argument", TRUE)
    /\ Apply(UnionOp, {{1}, {2}}) = {1, 2}
    /\ Print("DOMAIN as argument", TRUE)
    /\ Apply(DomainOp, <<5, 6, 7>>) = {1, 2, 3}
    /\ Print("ApplyTwice SUBSET", TRUE)
    /\ ApplyTwice(SubsetOp, {}) = {{}, {{}}}
    /\ Print("custom prefix -.", TRUE)
    /\ Apply(NegOp, {1, 2}) = {}
    /\ -. {3} = {}
    /\ Print("custom postfix ^+", TRUE)
    /\ Apply(SuccOp, {}) = {{}}
    /\ {} ^+ = {{}}
    /\ Print("custom postfix ^*", TRUE)
    /\ Apply(PowOp, {1}) = {{}, {1}}
    /\ {1} ^* = SUBSET {1}
    /\ Print("custom postfix ^#", TRUE)
    /\ Apply(BigUOp, {{1}, {2}}) = {1, 2}
    /\ {{1}, {2}} ^# = UNION {{1}, {2}}
    /\ Print("ApplyBoth", TRUE)
    /\ ApplyBoth(LAMBDA S : S ^* = SUBSET S, LAMBDA S : S ^# = UNION S, {{1}})
    /\ Print("LAMBDA wrapping SUBSET", TRUE)
    /\ Apply(LAMBDA S : SUBSET S, {}) = {{}}
    /\ Print(<<"all checks passed", Apply(SubsetOp, {1, 2})>>, TRUE)

=============================================================================