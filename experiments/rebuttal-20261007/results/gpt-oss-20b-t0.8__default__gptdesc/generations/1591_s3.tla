```
---- MODULE EvenOdd ----
EXTENDS Naturals, Sequences

CONSTANT N \in Nat          \* The natural number whose parity we compute

VARIABLES pc, stack, result, xEven, xOdd

(* A stack frame consists of the procedure name ("Even" or "Odd")
   and the current value of n for that call. *)
Frame == [proc : {"Even","Odd"}, n : Nat]

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ result = FALSE
  /\ xEven = FALSE
  /\ xOdd = FALSE

Next ==
  \/ (pc = "Start" /\
      pc'   = "EnterEven" /\
      stack'= <<[proc:"Even", n:N]>> \o stack /\
      UNCHANGED <<xEven,xOdd,result>>)

  \/ (pc = "EnterEven" /\ Len(stack) > 0 /\ LET f == Fst(stack) IN
        IF f.n = 0 THEN
           /\ xEven'   = TRUE
           /\ result'  = TRUE
           /\ stack'   = Tail(stack)
           /\ pc'      =
              IF Len(Tail(stack)) = 0
                 THEN "Done"
                 ELSE IF Fst(Tail(stack)).proc = "Even"
                      THEN "EnterEven"
                      ELSE "EnterOdd")
        ELSE
           /\ stack'   = <<[proc:"Odd", n:f.n-1]>> \o stack
           /\ pc'      = "EnterOdd"
           /\ UNCHANGED <<xEven,xOdd,result>>)

  \/ (pc = "EnterOdd" /\ Len(stack) > 0 /\ LET f == Fst(stack) IN
        IF f.n = 0 THEN
           /\ xOdd'    = FALSE
           /\ result'  = FALSE
           /\ stack'   = Tail(stack)
           /\ pc'      =
              IF Len(Tail(stack)) = 0
                 THEN "Done"
                 ELSE IF Fst(Tail(stack)).proc = "Even"
                      THEN "EnterEven"
                      ELSE "EnterOdd")
        ELSE
           /\ stack'   = <<[proc:"Even", n:f.n-1]>> \o stack
           /\ pc'      = "EnterEven"
           /\ UNCHANGED <<xEven,xOdd,result>>)

  \/ (pc = "Done" /\ UNCHANGED <<pc,stack,xEven,xOdd,result>>)

vars == {pc, stack, result, xEven, xOdd}

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_1(Next)
  /\ <> (pc = "Done")
```
```