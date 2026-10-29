------------------------------ MODULE ProcedureCalls ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

(* --algorithm ProcedureCalls
variables sum = 0, out = "";

procedure Add(a, b)
begin
  AddLbl:
    sum := a + b;
    return;
end procedure;

procedure IntToStr(n)
begin
  StrLbl:
    assert n = 10;
    out := ToString(n);
    return;
end procedure;

fair process main = 1
begin
  M1: call Add(3, 7);
  M2: call IntToStr(sum);
  M3: assert out = "10";
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES sum, out, pc, stack, a, b, n

vars == << sum, out, pc, stack, a, b, n >>

ProcSet == {1}

Init == /\ sum = 0
        /\ out = ""
        /\ a = [ self \in ProcSet |-> defaultInitValue ]
        /\ b = [ self \in ProcSet |-> defaultInitValue ]
        /\ n = [ self \in ProcSet |-> defaultInitValue ]
        /\ stack = [ self \in ProcSet |-> << >> ]
        /\ pc = [ self \in ProcSet |-> "M1" ]

AddLbl(self) == /\ pc[self] = "AddLbl"
                /\ sum' = a[self] + b[self]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << out, n >>

Add(self) == AddLbl(self)

StrLbl(self) == /\ pc[self] = "StrLbl"
                /\ Assert(n[self] = 10,
                          "Failure of assertion at line 18, column 5.")
                /\ out' = ToString(n[self])
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << sum, a, b >>

IntToStr(self) == StrLbl(self)

M1 == /\ pc[1] = "M1"
      /\ /\ a' = [a EXCEPT ![1] = 3]
         /\ b' = [b EXCEPT ![1] = 7]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "Add",
                                               pc        |-> "M2",
                                               a         |-> a[1],
                                               b         |-> b[1] ] >>
                                           \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "AddLbl"]
      /\ UNCHANGED << sum, out, n >>

M2 == /\ pc[1] = "M2"
      /\ /\ n' = [n EXCEPT ![1] = sum]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "IntToStr",
                                               pc        |-> "M3",
                                               n         |-> n[1] ] >>
                                           \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "StrLbl"]
      /\ UNCHANGED << sum, out, a, b >>

M3 == /\ pc[1] = "M3"
      /\ Assert(out = "10",
                "Failure of assertion at line 27, column 7.")
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << sum, out, stack, a, b, n >>

main == M1 \/ M2 \/ M3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet : Add(self) \/ IntToStr(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(main)
           /\ WF_vars(Add(1))
           /\ WF_vars(IntToStr(1))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

TypeOK == /\ pc[1] \in {"M1", "M2", "M3", "AddLbl", "StrLbl", "Done"}
          /\ sum \in Int
          /\ out \in STRING

Progress == (pc[1] = "M1") ~> (pc[1] = "Done")

FinalOutput == <>(out = "10")

=============================================================================