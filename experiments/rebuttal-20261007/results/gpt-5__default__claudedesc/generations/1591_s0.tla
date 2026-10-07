---- MODULE EvenOdd ----
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, result, stack, xEven, xOdd

PC == {
  "start",
  "Main_CallEven", "Main_AfterEven",
  "Even_entry", "Even_CallOdd", "Even_AfterOdd",
  "Odd_entry", "Odd_CallEven", "Odd_AfterEven",
  "Return", "Print", "Done"
}

CallFrame == [ret: PC]

vars == << pc, result, stack, xEven, xOdd >>

Init ==
  /\ pc = "start"
  /\ result \in BOOLEAN
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0

Start ==
  /\ pc = "start"
  /\ pc' = "Main_CallEven"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

MainCallEven ==
  /\ pc = "Main_CallEven"
  /\ stack' = Append(stack, [ret |-> "Main_AfterEven"])
  /\ xEven' = N
  /\ pc' = "Even_entry"
  /\ UNCHANGED << result, xOdd >>

EvenEntry0 ==
  /\ pc = "Even_entry"
  /\ xEven = 0
  /\ result' = TRUE
  /\ pc' = "Return"
  /\ UNCHANGED << stack, xEven, xOdd >>

EvenEntryNon0 ==
  /\ pc = "Even_entry"
  /\ xEven # 0
  /\ pc' = "Even_CallOdd"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

EvenCallOdd ==
  /\ pc = "Even_CallOdd"
  /\ stack' = Append(stack, [ret |-> "Even_AfterOdd"])
  /\ xOdd' = xEven - 1
  /\ pc' = "Odd_entry"
  /\ UNCHANGED << result, xEven >>

EvenAfterOdd ==
  /\ pc = "Even_AfterOdd"
  /\ pc' = "Return"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

OddEntry0 ==
  /\ pc = "Odd_entry"
  /\ xOdd = 0
  /\ result' = FALSE
  /\ pc' = "Return"
  /\ UNCHANGED << stack, xEven, xOdd >>

OddEntryNon0 ==
  /\ pc = "Odd_entry"
  /\ xOdd # 0
  /\ pc' = "Odd_CallEven"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

OddCallEven ==
  /\ pc = "Odd_CallEven"
  /\ stack' = Append(stack, [ret |-> "Odd_AfterEven"])
  /\ xEven' = xOdd - 1
  /\ pc' = "Even_entry"
  /\ UNCHANGED << result, xOdd >>

OddAfterEven ==
  /\ pc = "Odd_AfterEven"
  /\ pc' = "Return"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

DoReturn ==
  /\ pc = "Return"
  /\ Len(stack) > 0
  /\ LET top == stack[Len(stack)] IN
     LET rest == IF Len(stack) = 1 THEN << >> ELSE SubSeq(stack, 1, Len(stack) - 1) IN
       /\ stack' = rest
       /\ pc' = top.ret
       /\ UNCHANGED << result, xEven, xOdd >>

MainAfterEven ==
  /\ pc = "Main_AfterEven"
  /\ pc' = "Print"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

DoPrint ==
  /\ pc = "Print"
  /\ pc' = "Done"
  /\ UNCHANGED << result, stack, xEven, xOdd >>

Next ==
  \/ Start
  \/ MainCallEven
  \/ EvenEntry0
  \/ EvenEntryNon0
  \/ EvenCallOdd
  \/ EvenAfterOdd
  \/ OddEntry0
  \/ OddEntryNon0
  \/ OddCallEven
  \/ OddAfterEven
  \/ DoReturn
  \/ MainAfterEven
  \/ DoPrint

TypeOK ==
  /\ pc \in PC
  /\ result \in BOOLEAN
  /\ xEven \in Nat
  /\ xOdd \in Nat
  /\ stack \in Seq(CallFrame)

InOdd == pc = "Odd_entry"
CallOdd == pc = "Even_CallOdd"

PossibleCounts == TRUE

Termination == <> (pc = "Done")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

====