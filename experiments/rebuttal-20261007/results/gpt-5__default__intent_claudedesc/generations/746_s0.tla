------------------------------- MODULE Chameneos -------------------------------

EXTENDS Naturals

CONSTANTS M, N, InitColor

Colors == {"blue", "red", "yellow"}

Creatures == 1..M

Nil == "Nil"

ASSUME M \in Nat /\ M >= 1 /\ N \in Nat
ASSUME InitColor \in [Creatures -> Colors]

VARIABLES color, cnt, faded, waiting, total

RECURSIVE Sum(_,_)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

SumCnt == Sum(cnt, Creatures)

Third(c1, c2) == CHOOSE c \in Colors \ {c1, c2} : TRUE

Comp(c1, c2) == IF c1 = c2 THEN c1 ELSE Third(c1, c2)

TypeOK ==
  /\ color \in [Creatures -> Colors]
  /\ cnt \in [Creatures -> Nat]
  /\ faded \subseteq Creatures
  /\ waiting \in Creatures \cup {Nil}
  /\ total \in Nat /\ total <= N
  /\ waiting \in Creatures => waiting \notin faded
  /\ waiting \in Creatures => total < N

Init ==
  /\ color = InitColor
  /\ cnt = [i \in Creatures |-> 0]
  /\ faded = {}
  /\ waiting = Nil
  /\ total = 0
  /\ TypeOK

ArriveWait(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total < N
  /\ waiting = Nil
  /\ waiting' = i
  /\ UNCHANGED << color, cnt, faded, total >>

ArriveMeet(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total < N
  /\ waiting \in Creatures
  /\ waiting # i
  /\ waiting \notin faded
  /\ LET j == waiting
         newC == Comp(color[i], color[j])
     IN /\ waiting' = Nil
        /\ color' = [color EXCEPT ![i] = newC, ![j] = newC]
        /\ cnt'   = [cnt   EXCEPT ![i] = @ + 1, ![j] = @ + 1]
        /\ total' = total + 1
        /\ UNCHANGED faded

ArriveFade(i) ==
  /\ i \in Creatures
  /\ i \notin faded
  /\ total = N
  /\ faded' = faded \cup {i}
  /\ UNCHANGED << color, cnt, waiting, total >>

Next ==
  \E i \in Creatures :
      ArriveWait(i) \/ ArriveMeet(i) \/ ArriveFade(i)

Spec ==
  Init /\ [][Next]_<<color, cnt, faded, waiting, total>>

TypeInv == []TypeOK

SafetyAfterN == [] ( (total = N) => (SumCnt = 2 * N) )

Termination == <> (faded = Creatures)

=============================================================================