------------------------------- MODULE EvenOdd -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N
ASSUME N \in Nat

VARIABLES pc, stack, xEven, xOdd, ret, result

vars == << pc, stack, xEven, xOdd, ret, result >>

IsEmpty(s) == Len(s) = 0
Top(s) == s[Len(s)]
Pop(s) == IF Len(s) = 0 THEN s ELSE SubSeq(s, 1, Len(s) - 1)

EvCount(s) == Cardinality({ i \in 1..Len(s) : s[i] = "Even" })
OdCount(s) == Cardinality({ i \in 1..Len(s) : s[i] = "Odd" })

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = << >>
  /\ xOdd = << >>
  /\ ret = FALSE
  /\ result = FALSE

StartAct ==
  /\ pc = "Start"
  /\ pc' = "EvenCheck"
  /\ stack' = << "Even" >>
  /\ xEven' = << N >>
  /\ xOdd' = << >>
  /\ UNCHANGED << ret, result >>

EvenBaseAct ==
  /\ pc = "EvenCheck"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Even"
  /\ Len(xEven) > 0
  /\ Top(xEven) = 0
  /\ ret' = TRUE
  /\ stack' = Pop(stack)
  /\ xEven' = Pop(xEven)
  /\ pc' = "Return"
  /\ UNCHANGED << xOdd, result >>

EvenRecurseAct ==
  /\ pc = "EvenCheck"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Even"
  /\ Len(xEven) > 0
  /\ Top(xEven) > 0
  /\ stack' = Append(stack, "Odd")
  /\ xOdd' = Append(xOdd, Top(xEven) - 1)
  /\ pc' = "OddCheck"
  /\ UNCHANGED << xEven, ret, result >>

OddBaseAct ==
  /\ pc = "OddCheck"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Odd"
  /\ Len(xOdd) > 0
  /\ Top(xOdd) = 0
  /\ ret' = FALSE
  /\ stack' = Pop(stack)
  /\ xOdd' = Pop(xOdd)
  /\ pc' = "Return"
  /\ UNCHANGED << xEven, result >>

OddRecurseAct ==
  /\ pc = "OddCheck"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Odd"
  /\ Len(xOdd) > 0
  /\ Top(xOdd) > 0
  /\ stack' = Append(stack, "Even")
  /\ xEven' = Append(xEven, Top(xOdd) - 1)
  /\ pc' = "EvenCheck"
  /\ UNCHANGED << xOdd, ret, result >>

ReturnFromEvenAct ==
  /\ pc = "Return"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Even"
  /\ Len(xEven) > 0
  /\ stack' = Pop(stack)
  /\ xEven' = Pop(xEven)
  /\ pc' = "Return"
  /\ UNCHANGED << xOdd, ret, result >>

ReturnFromOddAct ==
  /\ pc = "Return"
  /\ ~IsEmpty(stack) /\ Top(stack) = "Odd"
  /\ Len(xOdd) > 0
  /\ stack' = Pop(stack)
  /\ xOdd' = Pop(xOdd)
  /\ pc' = "Return"
  /\ UNCHANGED << xEven, ret, result >>

FinishAct ==
  /\ pc = "Return"
  /\ IsEmpty(stack)
  /\ pc' = "Done"
  /\ result' = ret
  /\ UNCHANGED << stack, xEven, xOdd, ret >>

StutterAct ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
     StartAct
  \/ EvenBaseAct
  \/ EvenRecurseAct
  \/ OddBaseAct
  \/ OddRecurseAct
  \/ ReturnFromEvenAct
  \/ ReturnFromOddAct
  \/ FinishAct
  \/ StutterAct

TypeOK ==
  /\ pc \in { "Start", "EvenCheck", "OddCheck", "Return", "Done" }
  /\ stack \in Seq({ "Even", "Odd" })
  /\ xEven \in Seq(Nat)
  /\ xOdd \in Seq(Nat)
  /\ ret \in BOOLEAN
  /\ result \in BOOLEAN

StackTopHasParam ==
  /\ (~IsEmpty(stack) /\ Top(stack) = "Even") => Len(xEven) > 0
  /\ (~IsEmpty(stack) /\ Top(stack) = "Odd") => Len(xOdd) > 0

CountsOK ==
  /\ Len(xEven) = EvCount(stack)
  /\ Len(xOdd) = OdCount(stack)

Invariant == TypeOK /\ StackTopHasParam /\ CountsOK

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================