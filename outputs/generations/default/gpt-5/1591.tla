---- MODULE EvenOdd ----
EXTENDS Naturals, Sequences

CONSTANT N
ASSUME N \in Nat

VARIABLES pc, stack, xEven, xOdd, result

ProcNames == {"Even", "Odd"}
PC == {"Start", "DoEvenTest", "DoOddTest", "ReturnFromOdd", "ReturnFromEven", "PopReturn", "Finish", "Done"}
RetPC == {"ReturnFromOdd", "ReturnFromEven", "Finish"}
Frame == [proc: ProcNames, x: Nat, retpc: RetPC]

TypeOK ==
  /\ pc \in PC
  /\ stack \in Seq(Frame)
  /\ xEven \in Nat
  /\ xOdd \in Nat
  /\ result \in BOOLEAN

TopConsistent ==
  \/ Len(stack) = 0
  \/ LET f == Head(stack) IN
       /\ (f.proc = "Even" => xEven = f.x)
       /\ (f.proc = "Odd"  => xOdd  = f.x)

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven \in Nat
  /\ xOdd \in Nat
  /\ result \in BOOLEAN

StartStep ==
  /\ pc = "Start"
  /\ pc' = "DoEvenTest"
  /\ stack' = << [proc |-> "Even", x |-> N, retpc |-> "Finish"] >>
  /\ xEven' = N
  /\ UNCHANGED << xOdd, result >>

EvenBaseStep ==
  /\ pc = "DoEvenTest"
  /\ Len(stack) > 0
  /\ Head(stack).proc = "Even"
  /\ xEven = 0
  /\ result' = TRUE
  /\ pc' = "PopReturn"
  /\ UNCHANGED << stack, xEven, xOdd >>

EvenRecurseStep ==
  /\ pc = "DoEvenTest"
  /\ Len(stack) > 0
  /\ Head(stack).proc = "Even"
  /\ xEven > 0
  /\ stack' = << [proc |-> "Odd", x |-> xEven - 1, retpc |-> "ReturnFromOdd"] >> \o stack
  /\ xOdd' = xEven - 1
  /\ pc' = "DoOddTest"
  /\ UNCHANGED << xEven, result >>

OddBaseStep ==
  /\ pc = "DoOddTest"
  /\ Len(stack) > 0
  /\ Head(stack).proc = "Odd"
  /\ xOdd = 0
  /\ result' = FALSE
  /\ pc' = "PopReturn"
  /\ UNCHANGED << stack, xEven, xOdd >>

OddRecurseStep ==
  /\ pc = "DoOddTest"
  /\ Len(stack) > 0
  /\ Head(stack).proc = "Odd"
  /\ xOdd > 0
  /\ stack' = << [proc |-> "Even", x |-> xOdd - 1, retpc |-> "ReturnFromEven"] >> \o stack
  /\ xEven' = xOdd - 1
  /\ pc' = "DoEvenTest"
  /\ UNCHANGED << xOdd, result >>

ReturnFromOddStep ==
  /\ pc = "ReturnFromOdd"
  /\ pc' = "PopReturn"
  /\ UNCHANGED << stack, xEven, xOdd, result >>

ReturnFromEvenStep ==
  /\ pc = "ReturnFromEven"
  /\ pc' = "PopReturn"
  /\ UNCHANGED << stack, xEven, xOdd, result >>

PopReturnStep ==
  /\ pc = "PopReturn"
  /\ Len(stack) > 0
  /\ LET f == Head(stack) IN
     LET s' == Tail(stack) IN
       /\ stack' = s'
       /\ pc' = f.retpc
       /\ xEven' = IF Len(s') > 0 /\ Head(s').proc = "Even" THEN Head(s').x ELSE xEven
       /\ xOdd'  = IF Len(s') > 0 /\ Head(s').proc = "Odd"  THEN Head(s').x ELSE xOdd
       /\ UNCHANGED result

FinishStep ==
  /\ pc = "Finish"
  /\ pc' = "Done"
  /\ UNCHANGED << stack, xEven, xOdd, result >>

Next ==
  \/ StartStep
  \/ EvenBaseStep
  \/ EvenRecurseStep
  \/ OddBaseStep
  \/ OddRecurseStep
  \/ ReturnFromOddStep
  \/ ReturnFromEvenStep
  \/ PopReturnStep
  \/ FinishStep

vars == << pc, stack, xEven, xOdd, result >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Termination == <> (pc = "Done")

THEOREM Spec => []TypeOK
THEOREM Spec => []TopConsistent

====