---------------------------- MODULE ProcedureCalls ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT defaultInitValue

(* --algorithm ProcedureCalls
variables result = 0, output = "";

procedure Add(a, b)
begin
  AddStep:
    result := a + b;
    return;
end procedure;

procedure IntToStr(n)
begin
  ConvStep:
    assert n = 10;
    output := ToString(n);
    return;
end procedure;

fair process Main = 1
begin
  CallAdd:
    call Add(4, 6);
  CallConv:
    call IntToStr(result);
  Check:
    assert output = "10";
end process;
end algorithm; *)

VARIABLES result, output, pc, stack, a, b, n

vars == << result, output, pc, stack, a, b, n >>

ProcSet == {1}

Init == /\ result = 0
        /\ output = ""
        /\ a = [self \in ProcSet |-> defaultInitValue]
        /\ b = [self \in ProcSet |-> defaultInitValue]
        /\ n = [self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "CallAdd"]

(* Procedure Add *)
AddStep(self) == /\ pc[self] = "AddStep"
                 /\ result' = a[self] + b[self]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                 /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << output, n >>

Add(self) == AddStep(self)

(* Procedure IntToStr *)
ConvStep(self) == /\ pc[self] = "ConvStep"
                  /\ Assert(n[self] = 10,
                            "Failure of assertion: integer passed to IntToStr is not 10")
                  /\ output' = ToString(n[self])
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << result, a, b >>

IntToStr(self) == ConvStep(self)

(* Process Main *)
CallAdd(self) == /\ pc[self] = "CallAdd"
                 /\ /\ a' = [a EXCEPT ![self] = 4]
                    /\ b' = [b EXCEPT ![self] = 6]
                    /\ stack' = [stack EXCEPT ![self] =
                                   << [ procedure |-> "Add",
                                        pc        |-> "CallConv",
                                        a         |-> a[self],
                                        b         |-> b[self] ] >>
                                   \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "AddStep"]
                 /\ UNCHANGED << result, output, n >>

CallConv(self) == /\ pc[self] = "CallConv"
                  /\ /\ n' = [n EXCEPT ![self] = result]
                     /\ stack' = [stack EXCEPT ![self] =
                                    << [ procedure |-> "IntToStr",
                                         pc        |-> "Check",
                                         n         |-> n[self] ] >>
                                    \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "ConvStep"]
                  /\ UNCHANGED << result, output, a, b >>

Check(self) == /\ pc[self] = "Check"
               /\ Assert(output = "10",
                         "Failure of assertion: final output is not \"10\"")
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << result, output, stack, a, b, n >>

Main(self) == CallAdd(self) \/ CallConv(self) \/ Check(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ Main(1)
        \/ (\E self \in ProcSet : Add(self) \/ IntToStr(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Main(1))
        /\ WF_vars(Add(1))
        /\ WF_vars(IntToStr(1))

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ result \in Nat
          /\ pc \in [ProcSet -> {"CallAdd", "AddStep", "CallConv",
                                 "ConvStep", "Check", "Done"}]
          /\ stack \in [ProcSet -> Seq([procedure : {"Add", "IntToStr"},
                                        pc : {"CallConv", "Check"},
                                        a : Nat \cup {defaultInitValue},
                                        b : Nat \cup {defaultInitValue}]
                                    \cup [procedure : {"Add", "IntToStr"},
                                          pc : {"CallConv", "Check"},
                                          n : Nat \cup {defaultInitValue}])]

ConvArgIsTen == \A self \in ProcSet :
                   pc[self] = "ConvStep" => n[self] = 10

OutputCorrect == \A self \in ProcSet :
                   pc[self] \in {"Check", "Done"} => output = "10"

StackBounded == \A self \in ProcSet : Len(stack[self]) <= 1

(* Liveness properties *)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

EventuallyOutputTen == <>(output = "10")

OutputStaysTen == (output = "10") ~> [](output = "10")

CallAddLeadsToDone == \A self \in ProcSet :
                         (pc[self] = "CallAdd") ~> (pc[self] = "Done")

AddLeadsToConv == \A self \in ProcSet :
                     (pc[self] = "AddStep") ~> (pc[self] = "ConvStep")

=============================================================================