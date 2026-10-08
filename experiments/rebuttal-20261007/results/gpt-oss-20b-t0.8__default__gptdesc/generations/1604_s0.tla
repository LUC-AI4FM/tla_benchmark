```
----------------------------- MODULE ProcSpec -----------------------------
EXTENDS Naturals, Sequences

PROC_ADD == "Add"
PROC_STR == "StrConv"

VARIABLES pc, stack, globals, locals

IntToString(n) ==
  IF n = 10 THEN "10" ELSE ""

Init ==
  /\ pc = "Main_Start"
  /\ stack = <<>>
  /\ globals = [a |-> 10, b |-> 0, s |-> ""]
  /\ locals = [
        PROC_ADD -> [sum |-> 0],
        PROC_STR -> [intVal |-> 0]
      ]

Next ==
  \/ /\ pc = "Main_Start"
     /\ pc' = "Main_CallAdd"
     /\ stack' = stack
     /\ globals' = globals
     /\ locals' = locals

  \/ /\ pc = "Main_CallAdd"
     /\ pc' = "Add_Entry"
     /\ stack' = Append(stack, <<"Main_CallStrConv">>)
     /\ globals' = globals
     /\ locals' = locals

  \/ /\ pc = "Add_Entry"
     /\ locals' = [locals EXCEPT ![PROC_ADD] = [sum |-> globals.a]]
     /\ globals' = [globals EXCEPT ![b] = locals[PROC_ADD].sum]
     /\ pc' = "Add_Return"

  \/ /\ pc = "Add_Return"
     /\ LET ret == Last(stack) IN
        /\ stack' = SubSeq(stack, 1, Len(stack)-1)
        /\ pc' = ret

  \/ /\ pc = "Main_CallStrConv"
     /\ pc' = "StrConv_Entry"
     /\ stack' = Append(stack, <<"Main_Done">>)
     /\ globals' = globals
     /\ locals' = locals

  \/ /\ pc = "StrConv_Entry"
     /\ locals' = [locals EXCEPT ![PROC_STR] = [intVal |-> globals.b]]
     /\ globals' = [globals EXCEPT ![s] = IntToString(locals[PROC_STR].intVal)]
     /\ pc' = "StrConv_Return"

  \/ /\ pc = "StrConv_Return"
     /\ LET ret == Last(stack) IN
        /\ stack' = SubSeq(stack, 1, Len(stack)-1)
        /\ pc' = ret

  \/ /\ pc = "Main_Done"
     /\ pc' = "Main_Done"
     /\ stack' = stack
     /\ globals' = globals
     /\ locals' = locals

vars == <<pc, stack, globals, locals>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Inv1 ==
  (pc = "StrConv_Entry") => locals[PROC_STR].intVal = 10

Inv2 ==
  (pc \in {"Add_Return", "Main_CallStrConv"}) => globals.b = 10

Inv3 ==
  (pc = "Main_Done") => globals.s = "10"

Safety == Inv1 /\ Inv2 /\ Inv3
```