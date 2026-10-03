------------------------------- MODULE ProcCallModel -------------------------------

EXTENDS Integers, Sequences

CONSTANT Proc

ProcSet == {Proc}

Labels == {"start", "callAdd", "runProc", "afterAdd", "callStr", "afterStr", "Done"}
RetLabels == {"afterAdd", "afterStr"}
ProcNames == {"add", "toString"}

FrameType ==
  [ name: ProcNames,
    ret: RetLabels,
    a: Int, b: Int, n: Int ]

VARIABLES
  pc,            \* per-process program counter
  stack,         \* per-process activation-record stack (sequence of frames)
  sum,           \* per-process local integer result of addition
  outStr,        \* per-process local string result of int-to-string
  argStr,        \* per-process last integer argument passed to toString
  strCallIssued  \* per-process flag indicating toString call happened

vars == << pc, stack, sum, outStr, argStr, strCallIssued >>

ItoS(n) == IF n = 10 THEN "10" ELSE "not10"

Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s) - 1)
Push(s, x) == s \o << x >>

TypeOK ==
  /\ pc \in [ProcSet -> Labels]
  /\ stack \in [ProcSet -> Seq(FrameType)]
  /\ sum \in [ProcSet -> Int]
  /\ outStr \in [ProcSet -> { "", "10", "not10" }]
  /\ argStr \in [ProcSet -> Int]
  /\ strCallIssued \in [ProcSet -> BOOLEAN]

Init ==
  /\ pc = [p \in ProcSet |-> "start"]
  /\ stack = [p \in ProcSet |-> << >>]
  /\ sum = [p \in ProcSet |-> 0]
  /\ outStr = [p \in ProcSet |-> ""]
  /\ argStr = [p \in ProcSet |-> 0]
  /\ strCallIssued = [p \in ProcSet |-> FALSE]
  /\ TypeOK

Start(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "start"
  /\ pc' = [pc EXCEPT ![p] = "callAdd"]
  /\ UNCHANGED << stack, sum, outStr, argStr, strCallIssued >>

CallAdd(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "callAdd"
  /\ stack' = [stack EXCEPT ![p] = Push(stack[p],
                       [ name |-> "add",
                         ret  |-> "afterAdd",
                         a    |-> 7,
                         b    |-> 3,
                         n    |-> 0 ]) ]
  /\ pc' = [pc EXCEPT ![p] = "runProc"]
  /\ UNCHANGED << sum, outStr, argStr, strCallIssued >>

RunProcAdd(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "runProc"
  /\ Len(stack[p]) > 0
  /\ Top(stack[p]).name = "add"
  /\ LET fr == Top(stack[p]) IN
       /\ sum' = [sum EXCEPT ![p] = fr.a + fr.b]
       /\ stack' = [stack EXCEPT ![p] = Pop(stack[p])]
       /\ pc' = [pc EXCEPT ![p] = fr.ret]
       /\ UNCHANGED << outStr, argStr, strCallIssued >>

AfterAdd(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "afterAdd"
  /\ pc' = [pc EXCEPT ![p] = "callStr"]
  /\ UNCHANGED << stack, sum, outStr, argStr, strCallIssued >>

CallStr(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "callStr"
  /\ argStr' = [argStr EXCEPT ![p] = sum[p]]
  /\ strCallIssued' = [strCallIssued EXCEPT ![p] = TRUE]
  /\ stack' = [stack EXCEPT ![p] = Push(stack[p],
                       [ name |-> "toString",
                         ret  |-> "afterStr",
                         a    |-> 0,
                         b    |-> 0,
                         n    |-> sum[p] ]) ]
  /\ pc' = [pc EXCEPT ![p] = "runProc"]
  /\ UNCHANGED << sum, outStr >>

RunProcStr(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "runProc"
  /\ Len(stack[p]) > 0
  /\ Top(stack[p]).name = "toString"
  /\ LET fr == Top(stack[p]) IN
       /\ outStr' = [outStr EXCEPT ![p] = ItoS(fr.n)]
       /\ stack' = [stack EXCEPT ![p] = Pop(stack[p])]
       /\ pc' = [pc EXCEPT ![p] = fr.ret]
       /\ UNCHANGED << sum, argStr, strCallIssued >>

AfterStr(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "afterStr"
  /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED << stack, sum, outStr, argStr, strCallIssued >>

ProcAction(p) ==
  Start(p) \/ CallAdd(p) \/ RunProcAdd(p) \/ AfterAdd(p)
    \/ CallStr(p) \/ RunProcStr(p) \/ AfterStr(p)

Next ==
  \E p \in ProcSet: ProcAction(p)

Spec ==
  Init /\ [][Next]_vars /\ \A p \in ProcSet: WF_vars(ProcAction(p))

ArgToStringIs10 ==
  \A p \in ProcSet: strCallIssued[p] => argStr[p] = 10

FinalOutputIs10 ==
  \A p \in ProcSet: (pc[p] = "Done") => outStr[p] = "10"

Termination ==
  \A p \in ProcSet: <> (pc[p] = "Done")

FairProgressAdd ==
  \A p \in ProcSet: [](pc[p] = "callAdd" => <> (pc[p] = "afterAdd"))

FairProgressStr ==
  \A p \in ProcSet: [](pc[p] = "callStr" => <> (pc[p] = "afterStr"))

=============================================================================