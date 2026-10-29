---------------------------- MODULE PrePostOps ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

\* User-defined prefix and postfix operators

-a == {a}

a ^+ == a \cup {0}

a ^* == a \cup {1}

a ^# == SUBSET a

\* Higher-order operators that take a prefix or postfix operator as an argument

ApplyPre(Op(_), a) == Op(a)

ApplyPost(Op(_), a) == Op(a)

ApplyTemporal(Op(_), F) == Op(F)

\* Built-in prefix operators passed as arguments

PSubset(S) == ApplyPre(SUBSET, S)

PUnion(S) == ApplyPre(UNION, S)

PDomain(f) == ApplyPre(DOMAIN, f)

PNeg(a) == ApplyPre(-., a)

PEnabled(A) == ApplyPre(ENABLED, A)

PUnchanged(e) == ApplyPre(UNCHANGED, e)

PBox(F) == ApplyTemporal([], F)

PDiamond(F) == ApplyTemporal(<>, F)

\* Postfix operators passed as arguments

PPrime(e) == ApplyPost(', e)

PPlus(S) == ApplyPost(^+, S)

PStar(S) == ApplyPost(^*, S)

PHash(S) == ApplyPost(^#, S)

\* A tiny two-variable state machine over sets

Init == /\ x = {}
        /\ y = {}

AddX == /\ x = {}
        /\ PPrime(x) = {1}
        /\ PUnchanged(y)

AddY == /\ x # {}
        /\ y = {}
        /\ y' = PUnion({x, {2}})
        /\ UNCHANGED x

Done == /\ x # {}
        /\ y # {}
        /\ UNCHANGED vars

Next == AddX \/ AddY \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(AddX) /\ WF_vars(AddY)

TypeOK == /\ x \subseteq {1, 2}
          /\ y \subseteq {1, 2}

Property == /\ PBox(PDiamond(y # {}))
            /\ PBox((x = {}) => PEnabled(AddX))

ASSUME
  /\ Print(<<"SUBSET", PSubset({1})>>, TRUE)
  /\ PSubset({1}) = {{}, {1}}
  /\ PUnion({{1}, {2}}) = {1, 2}
  /\ PDomain(<<5, 6>>) = {1, 2}
  /\ PNeg(3) = {3}
  /\ PPlus({1}) = {0, 1}
  /\ PStar({0}) = {0, 1}
  /\ PHash({1}) = {{}, {1}}
  /\ Print(<<"custom", -7, {2}^+, {2}^*, {2}^#>>, TRUE)
  /\ Print("all prefix/postfix operator tests passed", TRUE)

=============================================================================