----------------------------- MODULE Chameneos -----------------------------
EXTENDS Naturals, Integers

CONSTANTS M, N, InitClr

VARIABLES col, met, faded, waiting, totMet

Colors == {"blue", "red", "yellow"}
Chameneos == 1..M
Null == "none"

TheThird(c1, c2) == CHOOSE c \in Colors : (c # c1) /\ (c # c2)
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE TheThird(c1, c2)

Init ==
  /\ col = InitClr
  /\ met = [c \in Chameneos |-> 0]
  /\ faded = [c \in Chameneos |-> FALSE]
  /\ waiting = Null
  /\ totMet = 0

ArriveAndWait(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ waiting = Null
  /\ totMet < N
  /\ waiting' = c
  /\ UNCHANGED <<col, met, faded, totMet>>

ArriveAndMeet(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ waiting \in Chameneos
  /\ c # waiting
  /\ totMet < N
  /\ LET w == waiting
         new == Complement(col[c], col[w])
     IN /\ col' = [col EXCEPT ![c] = new, ![w] = new]
        /\ met' = [met EXCEPT ![c] = @ + 1, ![w] = @ + 1]
        /\ faded' = faded
        /\ waiting' = Null
        /\ totMet' = totMet + 1

ArriveAndFade(c) ==
  /\ c \in Chameneos
  /\ ~faded[c]
  /\ totMet = N
  /\ faded' = [faded EXCEPT ![c] = TRUE]
  /\ UNCHANGED <<col, met, waiting, totMet>>

Next ==
  \E c \in Chameneos :
    ArriveAndWait(c) \/ ArriveAndMeet(c) \/ ArriveAndFade(c)

vars == <<col, met, faded, waiting, totMet>>

TypeOK ==
  /\ M \in Nat
  /\ N \in Nat
  /\ col \in [Chameneos -> Colors]
  /\ met \in [Chameneos -> Nat]
  /\ faded \in [Chameneos -> BOOLEAN]
  /\ waiting \in Chameneos \cup {Null}
  /\ totMet \in 0..N
  /\ InitClr \in [Chameneos -> Colors]

RECURSIVE SumUp(_)
SumUp(i) == IF i = 0 THEN 0 ELSE SumUp(i - 1) + met[i]
SumMet == SumUp(M)

Spec == Init /\ [][Next]_vars
============================================================================