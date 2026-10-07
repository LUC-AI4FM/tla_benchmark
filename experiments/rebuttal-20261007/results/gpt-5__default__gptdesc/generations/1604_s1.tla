----------------------------- MODULE ProcCalls -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT Pid

VARIABLES pc, x, y, intRes, strOut, stack

ProcSet == { Pid }

PCs ==
  {
    "start",
    "callAdd",
    "add_entry",
    "add_return",
    "afterAdd",
    "callItoA",
    "itoa_entry",
    "itoa_return",
    "afterItoA",
    "Done"
  }

RecType ==
  [ name : {"add", "itoa"},
    ret  : PCs,
    a    : Int,
    b    : Int,
    sum  : Int,
    n    : Int,
    s    : {"", "10"} ]

vars == << pc, x, y, intRes, strOut, stack >>

Init ==
  /\ pc      = [ i \in ProcSet |-> "start" ]
  /\ x       = [ i \in ProcSet |-> 0 ]
  /\ y       = [ i \in ProcSet |-> 0 ]
  /\ intRes  = [ i \in ProcSet |-> 0 ]
  /\ strOut  = [ i \in ProcSet |-> "" ]
  /\ stack   = [ i \in ProcSet |-> << >> ]

Start ==
  /\ pc[P] = "start"
  /\ x' = [x EXCEPT ![P] = 3]
  /\ y' = [y EXCEPT ![P] = 7]
  /\ pc' = [pc EXCEPT ![P] = "callAdd"]
  /\ UNCHANGED << intRes, strOut, stack >>
  \* where
  \*   P == Pid
  \* is used implicitly in all actions below
  \* (TLA+ allows free use of constants)

CallAdd ==
  /\ pc[P] = "callAdd"
  /\ LET st == stack[P]
         ar == [ name |-> "add",
                 ret  |-> "afterAdd",
                 a    |-> x[P],
                 b    |-> y[P],
                 sum  |-> 0,
                 n    |-> 0,
                 s    |-> "" ]
     IN /\ stack' = [stack EXCEPT ![P] = Append(st, ar)]
        /\ pc'    = [pc EXCEPT ![P] = "add_entry"]
        /\ UNCHANGED << x, y, intRes, strOut >>

AddEntry ==
  /\ pc[P] = "add_entry"
  /\ LET st == stack[P]
         fr == st[Len(st)]
         newfr ==
           [ fr EXCEPT !.sum = fr.a + fr.b ]
     IN /\ stack' =
            [ stack EXCEPT
                ![P] = [ i \in 1..Len(st) |-> IF i = Len(st) THEN newfr ELSE st[i] ] ]
        /\ pc' = [pc EXCEPT ![P] = "add_return"]
        /\ UNCHANGED << x, y, intRes, strOut >>

AddReturn ==
  /\ pc[P] = "add_return"
  /\ LET st == stack[P]
         fr == st[Len(st)]
         newStack == SubSeq(st, 1, Len(st) - 1)
     IN /\ intRes' = [intRes EXCEPT ![P] = fr.sum]
        /\ stack'  = [stack EXCEPT ![P] = newStack]
        /\ pc'     = [pc EXCEPT ![P] = fr.ret]
        /\ UNCHANGED << x, y, strOut >>

AfterAdd ==
  /\ pc[P] = "afterAdd"
  /\ pc' = [pc EXCEPT ![P] = "callItoA"]
  /\ UNCHANGED << x, y, intRes, strOut, stack >>

CallItoA ==
  /\ pc[P] = "callItoA"
  /\ Assert(intRes[P] = 10, "The integer passed to itoa must be 10")
  /\ LET st == stack[P]
         ar == [ name |-> "itoa",
                 ret  |-> "afterItoA",
                 a    |-> 0,
                 b    |-> 0,
                 sum  |-> 0,
                 n    |-> intRes[P],
                 s    |-> "" ]
     IN /\ stack' = [stack EXCEPT ![P] = Append(st, ar)]
        /\ pc'    = [pc EXCEPT ![P] = "itoa_entry"]
        /\ UNCHANGED << x, y, intRes, strOut >>

ItoaEntry ==
  /\ pc[P] = "itoa_entry"
  /\ LET st == stack[P]
         fr == st[Len(st)]
     IN /\ Assert(fr.n = 10, "itoa expects argument 10 in this model")
        /\ LET newfr == [ fr EXCEPT !.s = "10" ]
           IN /\ stack' =
                  [ stack EXCEPT
                      ![P] = [ i \in 1..Len(st) |-> IF i = Len(st) THEN newfr ELSE st[i] ] ]
              /\ pc' = [pc EXCEPT ![P] = "itoa_return"]
              /\ UNCHANGED << x, y, intRes, strOut >>

ItoaReturn ==
  /\ pc[P] = "itoa_return"
  /\ LET st == stack[P]
         fr == st[Len(st)]
         newStack == SubSeq(st, 1, Len(st) - 1)
     IN /\ strOut' = [strOut EXCEPT ![P] = fr.s]
        /\ stack'  = [stack EXCEPT ![P] = newStack]
        /\ pc'     = [pc EXCEPT ![P] = fr.ret]
        /\ UNCHANGED << x, y, intRes >>

AfterItoA ==
  /\ pc[P] = "afterItoA"
  /\ Assert(strOut[P] = "10", "The final output string must be 10")
  /\ pc' = [pc EXCEPT ![P] = "Done"]
  /\ UNCHANGED << x, y, intRes, strOut, stack >>

Stutter ==
  /\ pc[P] = "Done"
  /\ UNCHANGED vars

NextP ==
  Start \/ CallAdd \/ AddEntry \/ AddReturn
  \/ AfterAdd \/ CallItoA \/ ItoaEntry \/ ItoaReturn \/ AfterItoA

Next == NextP \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(NextP)

TypeOK ==
  /\ pc \in [ ProcSet -> PCs ]
  /\ x \in [ ProcSet -> Int ]
  /\ y \in [ ProcSet -> Int ]
  /\ intRes \in [ ProcSet -> Int ]
  /\ strOut \in [ ProcSet -> {"", "10"} ]
  /\ stack \in [ ProcSet -> Seq(RecType) ]

ItoaArgIs10 ==
  [](
     pc[P] \in {"itoa_entry", "itoa_return"}
     => /\ Len(stack[P]) >= 1
        /\ stack[P][Len(stack[P])].name = "itoa"
        /\ stack[P][Len(stack[P])].n = 10
   )

OutputStringIs10 ==
  []( pc[P] = "Done" => strOut[P] = "10" )

Termination ==
  <> (pc[P] = "Done")

=============================================================================