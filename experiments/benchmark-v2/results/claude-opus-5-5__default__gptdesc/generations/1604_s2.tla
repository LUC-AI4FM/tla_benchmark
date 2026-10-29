---------------------------- MODULE ProcedureCalls ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT MainId

ASSUME MainId \notin {}

(***************************************************************************
--algorithm ProcedureCalls {
    variables sum = 0, output = "";

    procedure Add(x = 0, y = 0) {
      AddLbl:
        sum := x + y;
        return;
    }

    procedure ToStr(n = 0) {
      ToStrLbl:
        assert n = 10;
        output := IntToStr(n);
        return;
    }

    fair process (Main = MainId) {
      M1: call Add(4, 6);
      M2: call ToStr(sum);
      M3: assert output = "10";
    }
}
***************************************************************************)

\* Helper: integer to string conversion (for non-negative integers)
Digit(d) ==
    CASE d = 0 -> "0"
      [] d = 1 -> "1"
      [] d = 2 -> "2"
      [] d = 3 -> "3"
      [] d = 4 -> "4"
      [] d = 5 -> "5"
      [] d = 6 -> "6"
      [] d = 7 -> "7"
      [] d = 8 -> "8"
      [] d = 9 -> "9"

RECURSIVE IntToStr(_)
IntToStr(k) ==
    IF k < 10 THEN Digit(k)
              ELSE IntToStr(k \div 10) \o Digit(k % 10)

\* BEGIN TRANSLATION
VARIABLES sum, output, pc, stack, x, y, n

vars == << sum, output, pc, stack, x, y, n >>

ProcSet == {MainId}

Init ==
    /\ sum = 0
    /\ output = ""
    /\ x = [self \in ProcSet |-> 0]
    /\ y = [self \in ProcSet |-> 0]
    /\ n = [self \in ProcSet |-> 0]
    /\ stack = [self \in ProcSet |-> << >>]
    /\ pc = [self \in ProcSet |-> "M1"]

\* Procedure Add
AddLbl(self) ==
    /\ pc[self] = "AddLbl"
    /\ sum' = x[self] + y[self]
    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
    /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
    /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED << output, n >>

Add(self) == AddLbl(self)

\* Procedure ToStr
ToStrLbl(self) ==
    /\ pc[self] = "ToStrLbl"
    /\ Assert(n[self] = 10,
              "Failure of assertion at line ToStrLbl: n = 10")
    /\ output' = IntToStr(n[self])
    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
    /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED << sum, x, y >>

ToStr(self) == ToStrLbl(self)

\* Process Main
M1 ==
    /\ pc[MainId] = "M1"
    /\ x' = [x EXCEPT ![MainId] = 4]
    /\ y' = [y EXCEPT ![MainId] = 6]
    /\ stack' = [stack EXCEPT ![MainId] =
                    << [ procedure |-> "Add",
                         pc        |-> "M2",
                         x         |-> x[MainId],
                         y         |-> y[MainId] ] >>
                    \o stack[MainId]]
    /\ pc' = [pc EXCEPT ![MainId] = "AddLbl"]
    /\ UNCHANGED << sum, output, n >>

M2 ==
    /\ pc[MainId] = "M2"
    /\ n' = [n EXCEPT ![MainId] = sum]
    /\ stack' = [stack EXCEPT ![MainId] =
                    << [ procedure |-> "ToStr",
                         pc        |-> "M3",
                         n         |-> n[MainId] ] >>
                    \o stack[MainId]]
    /\ pc' = [pc EXCEPT ![MainId] = "ToStrLbl"]
    /\ UNCHANGED << sum, output, x, y >>

M3 ==
    /\ pc[MainId] = "M3"
    /\ Assert(output = "10",
              "Failure of assertion at line M3: output = \"10\"")
    /\ pc' = [pc EXCEPT ![MainId] = "Done"]
    /\ UNCHANGED << sum, output, stack, x, y, n >>

Main == M1 \/ M2 \/ M3

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Main
    \/ (\E self \in ProcSet : Add(self) \/ ToStr(self))
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Main)
    /\ WF_vars(Add(MainId))
    /\ WF_vars(ToStr(MainId))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ sum \in Int
    /\ output \in STRING
    /\ pc \in [ProcSet -> {"M1", "M2", "M3", "AddLbl", "ToStrLbl", "Done"}]
    /\ x \in [ProcSet -> Int]
    /\ y \in [ProcSet -> Int]
    /\ n \in [ProcSet -> Int]
    /\ \A self \in ProcSet : Len(stack[self]) <= 1

\* The integer passed to the string conversion is 10
ToStrArgCorrect ==
    \A self \in ProcSet : pc[self] = "ToStrLbl" => n[self] = 10

\* The sum computed by Add is 10 once Add has returned
SumCorrect ==
    \A self \in ProcSet : pc[self] \in {"M2", "ToStrLbl", "M3", "Done"} => sum = 10

\* Final output string is "10"
OutputCorrect ==
    \A self \in ProcSet : pc[self] \in {"M3", "Done"} => output = "10"

\* Stack is empty whenever the process is executing in the main body
StackDiscipline ==
    \A self \in ProcSet :
        pc[self] \in {"M1", "M2", "M3", "Done"} => stack[self] = << >>

-----------------------------------------------------------------------------
\* Liveness properties

\* Every procedure call eventually returns
AddReturns ==
    \A self \in ProcSet : (pc[self] = "AddLbl") ~> (pc[self] = "M2")

ToStrReturns ==
    \A self \in ProcSet : (pc[self] = "ToStrLbl") ~> (pc[self] = "M3")

\* Fairness-based progress: from any point, the process eventually finishes
Progress ==
    \A self \in ProcSet : (pc[self] /= "Done") ~> (pc[self] = "Done")

\* Eventually the output is permanently "10"
EventuallyOutput == <>[](output = "10")

=============================================================================