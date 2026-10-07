------------------------------ MODULE EvenOdd ------------------------------

EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, stack, xEven, xOdd, res

Procs == {"Even", "Odd"}

PC == {"Start", "Even_entry", "Odd_entry", "ReturnFromOdd", "ReturnFromEven", "Done"}

Frame == [proc: Procs, x: Nat, ret: PC]

IsEmpty(s) == Len(s) = 0
Push(s, r) == Append(s, r)
Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)

vars == << pc, stack, xEven, xOdd, res >>

Init ==
  /\ N \in Nat
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven \in Nat
  /\ xOdd \in Nat
  /\ res \in BOOLEAN

Next ==
  \/ /\ pc = "Start"
     /\ stack' = Push(stack, [proc |-> "Even", x |-> N, ret |-> "Done"])
     /\ xEven' = N
     /\ UNCHANGED << xOdd, res >>
     /\ pc' = "Even_entry"

  \/ /\ pc = "Even_entry"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Even" /\ Top(stack).x = 0
     /\ LET f == Top(stack) IN
        /\ res' = TRUE
        /\ stack' = Pop(stack)
        /\ pc' = f.ret
     /\ UNCHANGED << xEven, xOdd >>

  \/ /\ pc = "Even_entry"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Even" /\ Top(stack).x > 0
     /\ LET x == Top(stack).x IN
        /\ stack' = Push(stack, [proc |-> "Odd", x |-> x - 1, ret |-> "ReturnFromOdd"])
        /\ xOdd' = x - 1
        /\ UNCHANGED << xEven, res >>
        /\ pc' = "Odd_entry"

  \/ /\ pc = "Odd_entry"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Odd" /\ Top(stack).x = 0
     /\ LET f == Top(stack) IN
        /\ res' = FALSE
        /\ stack' = Pop(stack)
        /\ pc' = f.ret
     /\ UNCHANGED << xEven, xOdd >>

  \/ /\ pc = "Odd_entry"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Odd" /\ Top(stack).x > 0
     /\ LET x == Top(stack).x IN
        /\ stack' = Push(stack, [proc |-> "Even", x |-> x - 1, ret |-> "ReturnFromEven"])
        /\ xEven' = x - 1
        /\ UNCHANGED << xOdd, res >>
        /\ pc' = "Even_entry"

  \/ /\ pc = "ReturnFromOdd"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Even"
     /\ LET f == Top(stack) IN
        /\ stack' = Pop(stack)
        /\ pc' = f.ret
     /\ UNCHANGED << xEven, xOdd, res >>

  \/ /\ pc = "ReturnFromEven"
     /\ ~IsEmpty(stack) /\ Top(stack).proc = "Odd"
     /\ LET f == Top(stack) IN
        /\ stack' = Pop(stack)
        /\ pc' = f.ret
     /\ UNCHANGED << xEven, xOdd, res >>

  \/ /\ pc = "Done"
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ pc \in PC
  /\ stack \in Seq(Frame)
  /\ xEven \in Nat
  /\ xOdd \in Nat
  /\ res \in BOOLEAN
  /\ IsEmpty(stack) \/ (Top(stack).proc = "Even" => xEven = Top(stack).x)
  /\ IsEmpty(stack) \/ (Top(stack).proc = "Odd"  => xOdd = Top(stack).x)

Termination == <> (pc = "Done")

=============================================================================