---------------------------- MODULE EvenOdd ----------------------------
EXTENDS Naturals, Sequences, TLC

N == 6

VARIABLES result, x, y, stack, pc, oddEntries, evenToOdd

vars == << result, x, y, stack, pc, oddEntries, evenToOdd >>

Init ==
    /\ result = FALSE
    /\ x = 0
    /\ y = 0
    /\ stack = << >>
    /\ pc = "Main"
    /\ oddEntries = 0
    /\ evenToOdd = 0

Frame(p) == [procedure |-> p, pc |-> "", x |-> x, y |-> y]

(* main: call Even(N) *)
Main ==
    /\ pc = "Main"
    /\ stack' = << [procedure |-> "Even", pc |-> "Print", x |-> x, y |-> y] >> \o stack
    /\ x' = N
    /\ pc' = "E1"
    /\ UNCHANGED << result, y, oddEntries, evenToOdd >>

(* procedure Even(x) *)
E1 ==
    /\ pc = "E1"
    /\ IF x = 0
         THEN /\ result' = TRUE
              /\ pc' = Head(stack).pc
              /\ x' = Head(stack).x
              /\ y' = Head(stack).y
              /\ stack' = Tail(stack)
              /\ UNCHANGED << oddEntries, evenToOdd >>
         ELSE /\ stack' = << [procedure |-> "Odd", pc |-> "E2", x |-> x, y |-> y] >> \o stack
              /\ y' = x - 1
              /\ pc' = "O1"
              /\ oddEntries' = oddEntries + 1
              /\ evenToOdd' = evenToOdd + 1
              /\ UNCHANGED << result, x >>

E2 ==
    /\ pc = "E2"
    /\ pc' = Head(stack).pc
    /\ x' = Head(stack).x
    /\ y' = Head(stack).y
    /\ stack' = Tail(stack)
    /\ UNCHANGED << result, oddEntries, evenToOdd >>

(* procedure Odd(y) *)
O1 ==
    /\ pc = "O1"
    /\ IF y = 0
         THEN /\ result' = FALSE
              /\ pc' = Head(stack).pc
              /\ x' = Head(stack).x
              /\ y' = Head(stack).y
              /\ stack' = Tail(stack)
              /\ UNCHANGED << oddEntries, evenToOdd >>
         ELSE /\ stack' = << [procedure |-> "Even", pc |-> "O2", x |-> x, y |-> y] >> \o stack
              /\ x' = y - 1
              /\ pc' = "E1"
              /\ UNCHANGED << result, y, oddEntries, evenToOdd >>

O2 ==
    /\ pc = "O2"
    /\ pc' = Head(stack).pc
    /\ x' = Head(stack).x
    /\ y' = Head(stack).y
    /\ stack' = Tail(stack)
    /\ UNCHANGED << result, oddEntries, evenToOdd >>

PrintRes ==
    /\ pc = "Print"
    /\ PrintT(result)
    /\ pc' = "Done"
    /\ UNCHANGED << result, x, y, stack, oddEntries, evenToOdd >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Main \/ E1 \/ E2 \/ O1 \/ O2 \/ PrintRes \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

(* Across all reachable states, Odd is entered (and Even->Odd taken)
   at most 3 times, and exactly 3 times once the computation is done. *)
PossibleCounts ==
    /\ oddEntries \in 0..3
    /\ evenToOdd \in 0..3
    /\ oddEntries = evenToOdd
    /\ (pc \in {"Print", "Done"}) => (oddEntries = 3 /\ evenToOdd = 3 /\ result = TRUE)

=============================================================================