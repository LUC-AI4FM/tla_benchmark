---------------------------- MODULE AddAndToString ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT defaultInitValue

(***************************************************************************
--algorithm AddAndToString {
    variables retInt = 0, retStr = "", output = "";

    procedure Add(a, b) {
      AddLbl:
        retInt := a + b;
        return;
    }

    procedure IntToStr(n) {
      ToStrLbl:
        assert n = 10;
        retStr := ToString(n);
        return;
    }

    fair process (main = 1) {
      P1: call Add(3, 7);
      P2: call IntToStr(retInt);
      P3: assert retStr = "10";
          output := retStr;
    }
}
 ***************************************************************************)

Digit(d) == CASE d = 0 -> "0"
              [] d = 1 -> "1"
              [] d = 2 -> "2"
              [] d = 3 -> "3"
              [] d = 4 -> "4"
              [] d = 5 -> "5"
              [] d = 6 -> "6"
              [] d = 7 -> "7"
              [] d = 8 -> "8"
              [] d = 9 -> "9"

RECURSIVE ToString(_)
ToString(i) == IF i < 10 THEN Digit(i)
               ELSE ToString(i \div 10) \o Digit(i % 10)

\* BEGIN TRANSLATION
VARIABLES retInt, retStr, output, pc, stack, a, b, n

vars == << retInt, retStr, output, pc, stack, a, b, n >>

ProcSet == {1}

Init == (* Global variables *)
        /\ retInt = 0
        /\ retStr = ""
        /\ output = ""
        (* Procedure Add *)
        /\ a = [self \in ProcSet |-> defaultInitValue]
        /\ b = [self \in ProcSet |-> defaultInitValue]
        (* Procedure IntToStr *)
        /\ n = [self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "P1"]

AddLbl(self) == /\ pc[self] = "AddLbl"
                /\ retInt' = a[self] + b[self]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << retStr, output, n >>

Add(self) == AddLbl(self)

ToStrLbl(self) == /\ pc[self] = "ToStrLbl"
                  /\ Assert(n[self] = 10,
                            "Failure of assertion: integer passed to IntToStr is not 10")
                  /\ retStr' = ToString(n[self])
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << retInt, output, a, b >>

IntToStr(self) == ToStrLbl(self)

P1 == /\ pc[1] = "P1"
      /\ /\ a' = [a EXCEPT ![1] = 3]
         /\ b' = [b EXCEPT ![1] = 7]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "Add",
                                                pc        |-> "P2",
                                                a         |-> a[1],
                                                b         |-> b[1] ] >>
                                            \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "AddLbl"]
      /\ UNCHANGED << retInt, retStr, output, n >>

P2 == /\ pc[1] = "P2"
      /\ /\ n' = [n EXCEPT ![1] = retInt]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |-> "IntToStr",
                                                pc        |-> "P3",
                                                n         |-> n[1] ] >>
                                            \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "ToStrLbl"]
      /\ UNCHANGED << retInt, retStr, output, a, b >>

P3 == /\ pc[1] = "P3"
      /\ Assert(retStr = "10",
                "Failure of assertion: final output string is not \"10\"")
      /\ output' = retStr
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << retInt, retStr, stack, a, b, n >>

main == P1 \/ P2 \/ P3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet : Add(self) \/ IntToStr(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(main) /\ WF_vars(Add(1)) /\ WF_vars(IntToStr(1))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety invariants *)

Labels == {"P1", "P2", "P3", "AddLbl", "ToStrLbl", "Done"}

TypeOK == /\ pc \in [ProcSet -> Labels]
          /\ retInt \in Nat
          /\ retStr \in {"", "10"}
          /\ output \in {"", "10"}
          /\ \A self \in ProcSet : stack[self] \in Seq(DOMAIN stack[self] \cup {})
                                   \/ TRUE

StackDepthOK == \A self \in ProcSet :
                   /\ (pc[self] \in {"AddLbl", "ToStrLbl"}) => Len(stack[self]) = 1
                   /\ (pc[self] \in {"P1", "P2", "P3", "Done"}) => Len(stack[self]) = 0

ArgIsTen == pc[1] = "ToStrLbl" => n[1] = 10

SumIsTen == pc[1] \in {"P2", "P3", "Done"} => retInt = 10

OutputCorrect == pc[1] = "Done" => output = "10"

-----------------------------------------------------------------------------
(* Liveness properties *)

EventuallyOutput == <>(output = "10")

Progress == (pc[1] = "P1") ~> (pc[1] = "Done")

CallsReturn == /\ (pc[1] = "AddLbl") ~> (pc[1] = "P2")
               /\ (pc[1] = "ToStrLbl") ~> (pc[1] = "P3")

StaysDone == [](pc[1] = "Done" => [](pc[1] = "Done" /\ output = "10"))

=============================================================================