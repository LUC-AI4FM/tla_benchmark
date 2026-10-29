---------------------------- MODULE PrefixPostfixArgs ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

-----------------------------------------------------------------------------
(* Higher-order operators taking a unary operator as argument               *)
-----------------------------------------------------------------------------

Pre(Op(_), a)  == Op(a)
Post(Op(_), a) == Op(a)
Twice(Op(_), a) == Op(Op(a))

-----------------------------------------------------------------------------
(* User-defined prefix and postfix operators                                *)
-----------------------------------------------------------------------------

-. S  == S \cup {0}
S ^+  == S \cup {2}
S ^*  == S \cup {3}
S ^#  == S \cup {4}

-----------------------------------------------------------------------------
(* Tiny state machine over sets                                             *)
-----------------------------------------------------------------------------

Init == /\ x = {}
        /\ y = {1}

Next == /\ Post(', x) = y
        /\ Post(', y) = x

Stutter == Pre(UNCHANGED, vars)

EnabledNext == Pre(ENABLED, Next)

TypeOK == /\ x \in Pre(SUBSET, {1})
          /\ y \in Pre(SUBSET, {1})

Spec == /\ Init
        /\ Pre([], [Next]_vars)
        /\ WF_vars(Next)

Property == Pre([], Pre(<>, x = {}))
AlsoProperty == Pre([], Pre(<>, y = {}))
NotStuck == Pre([], EnabledNext)

THEOREM Spec => Pre([], TypeOK)

-----------------------------------------------------------------------------
(* Assumptions checking parsing and evaluation of operator arguments        *)
-----------------------------------------------------------------------------

ASSUME
  /\ Print(<<"SUBSET", Pre(SUBSET, {1, 2})>>, TRUE)
  /\ Pre(SUBSET, {1}) = {{}, {1}}
  /\ Print(<<"UNION", Pre(UNION, {{1}, {2}})>>, TRUE)
  /\ Pre(UNION, {{1}, {2}}) = {1, 2}
  /\ Print(<<"DOMAIN", Pre(DOMAIN, <<5, 6>>)>>, TRUE)
  /\ Pre(DOMAIN, <<5, 6>>) = {1, 2}
  /\ Twice(SUBSET, {}) = {{}, {{}}}
  /\ Print(<<"-.", Pre(-., {1})>>, TRUE)
  /\ Pre(-., {1}) = {0, 1}
  /\ -{1} = {0, 1}
  /\ Print(<<"^+", Post(^+, {1})>>, TRUE)
  /\ Post(^+, {1}) = {1, 2}
  /\ Post(^*, {1}) = {1, 3}
  /\ Post(^#, {1}) = {1, 4}
  /\ {1}^+ = {1, 2}
  /\ Twice(^+, {1}) = {1, 2}

=============================================================================