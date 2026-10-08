------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES stack, result, pc

(* Frame: [proc : {"Even","Odd"}, x : Nat, pc : {"Start","AfterCall"}] *)

Init ==
  /\ stack = << [proc |-> "Even", x |-> N, pc |-> "Start"] >>
  /\ result = FALSE
  /\ pc = "Start"

Next ==
  IF Len(stack) = 0 THEN
     UNCHANGED <<stack,result,pc>>
  ELSE
    LET f == LAST(stack)
        rest == SubSeq(stack, 1, Len(stack)-1)
    IN
      CASE f.proc = "Even" /\ f.pc = "Start" ->
            IF f.x = 0 THEN
               /\ result' = TRUE
               /\ stack' = rest
            ELSE
               /\ stack' = rest ++ << [proc |-> "Even", x |-> f.x, pc |-> "AfterCall"],
                                      [proc |-> "Odd",  x |-> f.x - 1, pc |-> "Start"] >>
               /\ result' = result
      [] f.proc = "Even" /\ f.pc = "AfterCall" ->
            /\ stack' = rest
            /\ result' = result
      [] f.proc = "Odd" /\ f.pc = "Start" ->
            IF f.x = 1 THEN
               /\ result' = TRUE
               /\ stack' = rest
            ELSE
               /\ stack' = rest ++ << [proc |-> "Odd",  x |-> f.x, pc |-> "AfterCall"],
                                      [proc |-> "Even", x |-> f.x - 1, pc |-> "Start"] >>
               /\ result' = result
      [] f.proc = "Odd" /\ f.pc = "AfterCall" ->
            /\ stack' = rest
            /\ result' = result
    /\ pc' = IF Len(stack') = 0 THEN "Done" ELSE LAST(stack').pc

Spec == Init /\ [][Next]_<<stack,result,pc>> /\ WF_0(Next)

THEOREM Termination == []<> (pc = "Done")
=============================================================================