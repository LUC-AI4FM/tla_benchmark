---------------------------- MODULE ProcCall_OneFairProcess ----------------------------
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS p

Proc == {p}

PC == {"start", "add_call", "add_body", "add_ret",
       "afterAdd", "str_call", "toStr_body", "str_ret",
       "afterStr", "Done"}

ProcNames == {"add", "toStr"}

Frame == [proc: ProcNames, retpc: PC]

VARIABLES pc, stack, l_add_x, l_add_y, l_str_n, rv, outStr

vars == << pc, stack, l_add_x, l_add_y, l_str_n, rv, outStr >>

None == "None"

StackTop(s) == s[Len(s)]
StackPop(s) == IF Len(s) = 0 THEN s ELSE SubSeq(s, 1, Len(s) - 1)
Push(s, f) == Append(s, f)

IntToString(n) == IF n = 10 THEN "10" ELSE "not10"

TypeOK ==
  /\ pc \in [Proc -> PC]
  /\ stack \in [Proc -> Seq(Frame)]
  /\ l_add_x \in [Proc -> Int]
  /\ l_add_y \in [Proc -> Int]
  /\ l_str_n \in [Proc -> Int]
  /\ rv \in [Proc -> (Int \cup {"10", "not10", None})]
  /\ outStr \in {"", "10", "not10"}

Init ==
  /\ pc = [self \in Proc |-> "start"]
  /\ stack = [self \in Proc |-> <<>>]
  /\ l_add_x = [self \in Proc |-> 0]
  /\ l_add_y = [self \in Proc |-> 0]
  /\ l_str_n = [self \in Proc |-> 0]
  /\ rv = [self \in Proc |-> None]
  /\ outStr = ""

CallAdd(self) ==
  /\ self \in Proc
  /\ pc[self] = "start"
  /\ l_add_x' = [l_add_x EXCEPT ![self] = 7]
  /\ l_add_y' = [l_add_y EXCEPT ![self] = 3]
  /\ stack' = [stack EXCEPT ![self] = Push(stack[self], [proc |-> "add", retpc |-> "afterAdd"])]
  /\ pc' = [pc EXCEPT ![self] = "add_body"]
  /\ UNCHANGED << l_str_n, rv, outStr >>

AddBody(self) ==
  /\ self \in Proc
  /\ pc[self] = "add_body"
  /\ rv' = [rv EXCEPT ![self] = l_add_x[self] + l_add_y[self]]
  /\ pc' = [pc EXCEPT ![self] = "add_ret"]
  /\ UNCHANGED << stack, l_add_x, l_add_y, l_str_n, outStr >>

ReturnFromAdd(self) ==
  /\ self \in Proc
  /\ pc[self] = "add_ret"
  /\ stack[self] # <<>>
  /\ LET top == StackTop(stack[self]) IN
       /\ top.proc = "add"
       /\ pc' = [pc EXCEPT ![self] = top.retpc]
       /\ stack' = [stack EXCEPT ![self] = StackPop(stack[self])]
  /\ UNCHANGED << l_add_x, l_add_y, l_str_n, rv, outStr >>

CallStr(self) ==
  /\ self \in Proc
  /\ pc[self] = "afterAdd"
  /\ Assert(rv[self] = 10, "Argument to string conversion must be 10")
  /\ l_str_n' = [l_str_n EXCEPT ![self] = rv[self]]
  /\ stack' = [stack EXCEPT ![self] = Push(stack[self], [proc |-> "toStr", retpc |-> "afterStr"])]
  /\ pc' = [pc EXCEPT ![self] = "toStr_body"]
  /\ UNCHANGED << l_add_x, l_add_y, rv, outStr >>

ToStrBody(self) ==
  /\ self \in Proc
  /\ pc[self] = "toStr_body"
  /\ rv' = [rv EXCEPT ![self] = IntToString(l_str_n[self])]
  /\ pc' = [pc EXCEPT ![self] = "str_ret"]
  /\ UNCHANGED << stack, l_add_x, l_add_y, l_str_n, outStr >>

ReturnFromStr(self) ==
  /\ self \in Proc
  /\ pc[self] = "str_ret"
  /\ stack[self] # <<>>
  /\ LET top == StackTop(stack[self]) IN
       /\ top.proc = "toStr"
       /\ pc' = [pc EXCEPT ![self] = top.retpc]
       /\ stack' = [stack EXCEPT ![self] = StackPop(stack[self])]
  /\ UNCHANGED << l_add_x, l_add_y, l_str_n, rv, outStr >>

AfterStr(self) ==
  /\ self \in Proc
  /\ pc[self] = "afterStr"
  /\ outStr' = rv[self]
  /\ Assert(outStr' = "10", "Final output must be the string \"10\"")
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << stack, l_add_x, l_add_y, l_str_n, rv >>

ProcNext(self) ==
    CallAdd(self)
  \/ AddBody(self)
  \/ ReturnFromAdd(self)
  \/ CallStr(self)
  \/ ToStrBody(self)
  \/ ReturnFromStr(self)
  \/ AfterStr(self)

Next ==
  \E self \in Proc: ProcNext(self)

ArgIs10 ==
  \A self \in Proc:
    (pc[self] \in {"toStr_body", "str_ret", "afterStr", "Done"}) => l_str_n[self] = 10

OutIs10AtEnd ==
  (pc[p] = "Done") => outStr = "10"

SafetyInv == TypeOK /\ ArgIs10 /\ OutIs10AtEnd

Termination == <> (pc[p] = "Done")
OutputEventuallyCorrect == <> (outStr = "10")

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(ProcNext(p))

=============================================================================