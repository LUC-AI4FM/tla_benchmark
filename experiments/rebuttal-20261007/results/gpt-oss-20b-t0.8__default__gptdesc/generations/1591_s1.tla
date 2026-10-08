------------------------------ MODULE EvenOddSpec ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N  \in Nat

VARIABLES S, pc, res

vars == <<S, pc, res>>

Init ==
  /\ S = << [proc |-> "Even", pc |-> "EvenStart",
              xEven |-> N, xOdd |-> 0] >>
  /\ pc = "EvenStart"
  /\ res = FALSE

/* Helper to get top frame of the stack */
TopRec(S) == IF Len(S) > 0 THEN S[1] ELSE <<>>

/* Update the top frame with a new record F */
UpdateTop(F, S) ==
  LET Rest == Tail(S)
  IN Prepend(F, Rest)

/* ---- Even procedure actions ---- */

EvenStart ==
  /\ TopRec(S).proc = "Even"
  /\ pc = "EvenStart"
  /\ LET NewRec == [TopRec(S) EXCEPT !.pc = "EvenCheck"]
     IN S' = UpdateTop(NewRec, S)
      /\ pc' = "EvenCheck"

EvenCheckZero ==
  /\ TopRec(S).proc = "Even"
  /\ pc = "EvenCheck"
  /\ TopRec(S).xEven = 0
  /\ LET NewRec == [TopRec(S) EXCEPT !.pc = "EvenZero"]
     IN S' = UpdateTop(NewRec, S)
      /\ pc' = "EvenZero"

EvenCallOdd ==
  /\ TopRec(S).proc = "Even"
  /\ pc = "EvenCheck"
  /\ TopRec(S).xEven /= 0
  /\ LET NewEven == [TopRec(S) EXCEPT !.pc = "EvenReturn"]
     /\ Rest == Tail(Tail(S))
     /\ NewOdd == [proc |-> "Odd", pc |-> "OddCheck",
                   xEven |-> 0, xOdd |-> TopRec(S).xEven - 1]
     IN S' = <<NewOdd, NewEven>> ++ Rest
      /\ pc' = "OddCheck"

EvenAfterOdd ==
  /\ TopRec(S).proc = "Even"
  /\ pc = "EvenReturn"
  /\ LET NewS == Tail(S)
     IN S' = NewS
      /\ res' = ~res
      /\ IF Len(NewS) > 0 THEN pc' = [TopRec(NewS)].pc ELSE pc' = "Done"

EvenZero ==
  /\ TopRec(S).proc = "Even"
  /\ pc = "EvenZero"
  /\ LET NewS == Tail(S)
     IN S' = NewS
      /\ res' = TRUE
      /\ IF Len(NewS) > 0 THEN pc' = [TopRec(NewS)].pc ELSE pc' = "Done"

/* ---- Odd procedure actions ---- */

OddCheckZero ==
  /\ TopRec(S).proc = "Odd"
  /\ pc = "OddCheck"
  /\ TopRec(S).xOdd = 0
  /\ LET NewRec == [TopRec(S) EXCEPT !.pc = "OddZero"]
     IN S' = UpdateTop(NewRec, S)
      /\ pc' = "OddZero"

OddCheckNonZero ==
  /\ TopRec(S).proc = "Odd"
  /\ pc = "OddCheck"
  /\ TopRec(S).xOdd /= 0
  /\ LET NewOdd == [TopRec(S) EXCEPT !.pc = "OddReturn"]
     /\ Rest == Tail(Tail(S))
     /\ NewEven == [proc |-> "Even", pc |-> "EvenCheck",
                    xEven |-> TopRec(S).xOdd - 1, xOdd |-> 0]
     IN S' = <<NewEven, NewOdd>> ++ Rest
      /\ pc' = "EvenCheck"

OddAfterEven ==
  /\ TopRec(S).proc = "Odd"
  /\ pc = "OddReturn"
  /\ LET NewS == Tail(S)
     IN S' = NewS
      /\ res' = ~res
      /\ IF Len(NewS) > 0 THEN pc' = [TopRec(NewS)].pc ELSE pc' = "Done"

OddZero ==
  /\ TopRec(S).proc = "Odd"
  /\ pc = "OddZero"
  /\ LET NewS == Tail(S)
     IN S' = NewS
      /\ res' = FALSE
      /\ IF Len(NewS) > 0 THEN pc' = [TopRec(NewS)].pc ELSE pc' = "Done"

/* ---- Stuttering after termination ---- */

Terminate ==
  /\ Len(S) = 0
  /\ pc' = pc
  /\ res' = res
  /\ S' = S

/* Next relation is the disjunction of all enabled actions */
Next == EvenStart \/ EvenCheckZero \/ EvenCallOdd \/ EvenAfterOdd \/ EvenZero \/
        OddCheckZero \/ OddCheckNonZero \/ OddAfterEven \/ OddZero \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ <> (pc = "Done")
=============================================================================