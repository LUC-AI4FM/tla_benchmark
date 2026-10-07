----------------------------- MODULE EvenOdd -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

VARIABLES pc, stack, result

ProcSet == {"Even", "Odd"}
LocSet  == {"entry", "even_cont", "odd_cont"}

ActivationRecSet ==
  [ proc: ProcSet,
    loc: LocSet,
    xEven: Nat,
    xOdd:  Nat ]

SeqOfRecs == Seq(ActivationRecSet)

Pop(s) ==
  IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

ReplaceTop(s, e) ==
  [ i \in 1..Len(s) |-> IF i = Len(s) THEN e ELSE s[i] ]

TypeOK ==
  /\ pc \in {"Start", "Run", "Done"}
  /\ stack \in SeqOfRecs
  /\ result \in BOOLEAN

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ result \in BOOLEAN

StartStep ==
  /\ pc = "Start"
  /\ stack' =
        << [ proc |-> "Even",
             loc  |-> "entry",
             xEven |-> N,
             xOdd  |-> 0 ] >>
  /\ pc' = "Run"
  /\ UNCHANGED result

EvenEntryBase ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Even"
       /\ fr.loc  = "entry"
       /\ fr.xEven = 0
  /\ LET newStack == Pop(stack) IN
       /\ stack' = newStack
       /\ result' = TRUE
       /\ pc' = IF Len(newStack) = 0 THEN "Done" ELSE "Run"

EvenEntryRec ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Even"
       /\ fr.loc  = "entry"
       /\ fr.xEven > 0
       /\ LET s1 == ReplaceTop(stack, [fr EXCEPT !.loc = "even_cont"]) IN
             stack' =
               Append(s1,
                      [ proc |-> "Odd",
                        loc  |-> "entry",
                        xEven |-> 0,
                        xOdd  |-> fr.xEven - 1 ])
  /\ pc' = "Run"
  /\ UNCHANGED result

EvenCont ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Even"
       /\ fr.loc  = "even_cont"
  /\ LET newStack == Pop(stack) IN
       /\ stack' = newStack
       /\ pc' = IF Len(newStack) = 0 THEN "Done" ELSE "Run"
       /\ UNCHANGED result

OddEntryBase ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Odd"
       /\ fr.loc  = "entry"
       /\ fr.xOdd = 0
  /\ LET newStack == Pop(stack) IN
       /\ stack' = newStack
       /\ result' = FALSE
       /\ pc' = IF Len(newStack) = 0 THEN "Done" ELSE "Run"

OddEntryRec ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Odd"
       /\ fr.loc  = "entry"
       /\ fr.xOdd > 0
       /\ LET s1 == ReplaceTop(stack, [fr EXCEPT !.loc = "odd_cont"]) IN
             stack' =
               Append(s1,
                      [ proc |-> "Even",
                        loc  |-> "entry",
                        xEven |-> fr.xOdd - 1,
                        xOdd  |-> 0 ])
  /\ pc' = "Run"
  /\ UNCHANGED result

OddCont ==
  /\ pc = "Run"
  /\ Len(stack) > 0
  /\ LET fr == stack[Len(stack)] IN
       /\ fr.proc = "Odd"
       /\ fr.loc  = "odd_cont"
  /\ LET newStack == Pop(stack) IN
       /\ stack' = newStack
       /\ pc' = IF Len(newStack) = 0 THEN "Done" ELSE "Run"
       /\ UNCHANGED result

Next ==
  \/ StartStep
  \/ EvenEntryBase
  \/ EvenEntryRec
  \/ EvenCont
  \/ OddEntryBase
  \/ OddEntryRec
  \/ OddCont

Vars == << pc, stack, result >>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Next)

Termination ==
  <> (pc = "Done")

=============================================================================