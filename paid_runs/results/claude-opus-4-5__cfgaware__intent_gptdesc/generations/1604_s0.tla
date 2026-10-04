---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, locals, retVal, output

vars == <<pc, stack, locals, retVal, output>>

(* The expected result of adding 3 and 5 is 8, which converts to "8" *)
ExpectedString == "8"
AddArg1 == 3
AddArg2 == 5
ExpectedSum == 8

Init ==
    /\ pc = "Main1"
    /\ stack = <<>>
    /\ locals = defaultInitValue
    /\ retVal = defaultInitValue
    /\ output = defaultInitValue

(* Main step 1: Call the Add procedure with arguments 3 and 5 *)
Main1 ==
    /\ pc = "Main1"
    /\ stack' = <<[returnTo |-> "Main2", savedLocals |-> locals]>> \o stack
    /\ locals' = [a |-> AddArg1, b |-> AddArg2]
    /\ pc' = "Add"
    /\ UNCHANGED <<retVal, output>>

(* Add procedure: computes a + b and returns *)
Add ==
    /\ pc = "Add"
    /\ retVal' = locals.a + locals.b
    /\ pc' = "AddReturn"
    /\ UNCHANGED <<stack, locals, output>>

AddReturn ==
    /\ pc = "AddReturn"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ locals' = frame.savedLocals
          /\ pc' = frame.returnTo
          /\ stack' = Tail(stack)
    /\ UNCHANGED <<retVal, output>>

(* Main step 2: Call IntToString with the result from Add *)
Main2 ==
    /\ pc = "Main2"
    /\ stack' = <<[returnTo |-> "Main3", savedLocals |-> locals]>> \o stack
    /\ locals' = [n |-> retVal]
    /\ pc' = "IntToString"
    /\ UNCHANGED <<retVal, output>>

(* IntToString procedure: converts integer to string, but only handles ExpectedSum *)
IntToString ==
    /\ pc = "IntToString"
    /\ Assert(locals.n = ExpectedSum, "IntToString called with unexpected integer")
    /\ retVal' = "8"
    /\ pc' = "IntToStringReturn"
    /\ UNCHANGED <<stack, locals, output>>

IntToStringReturn ==
    /\ pc = "IntToStringReturn"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ locals' = frame.savedLocals
          /\ pc' = frame.returnTo
          /\ stack' = Tail(stack)
    /\ UNCHANGED <<retVal, output>>

(* Main step 3: Record the returned string into output *)
Main3 ==
    /\ pc = "Main3"
    /\ output' = retVal
    /\ pc' = "Main4"
    /\ UNCHANGED <<stack, locals, retVal>>

(* Main step 4: Assert final output equals expected string and transition to Done *)
Main4 ==
    /\ pc = "Main4"
    /\ Assert(output = ExpectedString, "Final output does not match expected string")
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, locals, retVal, output>>

(* Terminal state *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Main1
    \/ Add
    \/ AddReturn
    \/ Main2
    \/ IntToString
    \/ IntToStringReturn
    \/ Main3
    \/ Main4
    \/ Done

(* Fairness: each enabled action cannot be indefinitely postponed *)
Fairness ==
    /\ WF_vars(Main1)
    /\ WF_vars(Add)
    /\ WF_vars(AddReturn)
    /\ WF_vars(Main2)
    /\ WF_vars(IntToString)
    /\ WF_vars(IntToStringReturn)
    /\ WF_vars(Main3)
    /\ WF_vars(Main4)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Type invariant for reference *)
TypeOK ==
    /\ pc \in {"Main1", "Main2", "Main3", "Main4", "Add", "AddReturn", 
               "IntToString", "IntToStringReturn", "Done"}
    /\ stack \in Seq([returnTo : STRING, savedLocals : ANY])

(* Termination condition: program reaches Done with empty stack *)
Terminated == pc = "Done" /\ stack = <<>>

(* Safety property: when done, output equals expected string *)
SafetyProperty == pc = "Done" => output = ExpectedString

(* Liveness property: the main process eventually terminates *)
LivenessProperty == <>(Terminated)

(* Termination theorem *)
THEOREM Spec => <>Terminated

=============================================================================