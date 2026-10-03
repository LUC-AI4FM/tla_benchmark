---------------------------- MODULE PlusCalModel ----------------------------
EXTENDS Integers, Strings

CONSTANT ProcSet
VARIABLE pc, x, stack, output

ProcType == {"Addition", "ToString"}

VarType == [x: Int]

RecType == [proc: ProcType, vars: VarType]

defaultInitValue == <<0, [], "">> 

Spec ==
  /\ pc \in [p \in ProcSet |-> "Start"]
  /\ x = [p \in ProcSet |-> 0]
  /\ stack = [p \in ProcSet |-> <<>>]
  /\ output = [p \in ProcSet |-> ""]
  /\ WF_vars(ProcSet, pc, x, stack)
  /\ SF_vars(ProcSet, pc, x, stack)

TypeOK ==
  /\ pc \in [ProcSet -> {"Start", "Addition", "ToString", "Done"}]
  /\ x \in [ProcSet -> Int]
  /\ stack \in [ProcSet -> Seq(RecType)]
  /\ output \in [ProcSet -> String]

Next(p) ==
  /\ TypeOK
  /\ IF pc[p] = "Start"
    THEN /\ pc' = [pc EXCEPT ![p] = "Addition"]
         /\ x' = [x EXCEPT ![p] = 5]
         /\ stack' = [stack EXCEPT ![p] = <<[proc |-> "Addition", vars |-> [x |-> 5]]>>]
         /\ output' = output
    ELSE IF pc[p] = "Addition"
      THEN /\ pc' = [pc EXCEPT ![p] = "ToString"]
           /\ x' = [x EXCEPT ![p] = 10]
           /\ stack' = [stack EXCEPT ![p] = <<[proc |-> "ToString", vars |-> [x |-> 10]]>>]
           /\ output' = output
      ELSE IF pc[p] = "ToString"
        THEN /\ pc' = [pc EXCEPT ![p] = "Done"]
             /\ x' = x
             /\ stack' = [stack EXCEPT ![p] = <<>>]
             /\ output' = [output EXCEPT ![p] = "10"]
      ELSE /\ pc' = pc
           /\ x' = x
           /\ stack' = stack
           /\ output' = output

WF_vars(ProcSet, pc, x, stack) ==
  \A p \in ProcSet : 
    (pc[p] = "Start" => <>(pc[p] = "Addition"))
    /\ (pc[p] = "Addition" => <>(pc[p] = "ToString"))
    /\ (pc[p] = "ToString" => <>(pc[p] = "Done"))

SF_vars(ProcSet, pc, x, stack) ==
  \A p \in ProcSet : 
    (pc[p] = "Start" => <>[](pc[p] = "Addition"))
    /\ (pc[p] = "Addition" => <>[](pc[p] = "ToString"))
    /\ (pc[p] = "ToString" => <>[](pc[p] = "Done"))

THEOREM Spec => []<>(output[1] = "10")
=============================================================================