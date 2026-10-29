--------------------------- MODULE CallAddToString ---------------------------
EXTENDS Naturals, Sequences, TLC

(***************************************************************************
--algorithm CallAddToString {
    variables intRet = 0, strRet = "";

    procedure Add(a, b) {
      AddLbl:
        intRet := a + b;
        return;
    }

    procedure ToString(n) {
      StrLbl:
        assert n = 10;
        strRet := IntToStr(n);
        return;
    }

    fair process (Main = 1)
      variables x = 0, s = "";
    {
      Start:
        call Add(4, 6);
      SaveX:
        x := intRet;
        call ToString(x);
      Finish:
        s := strRet;
        assert s = "10";
    }
}
***************************************************************************)

Digit(d) == CASE d = 0 -> "0" [] d = 1 -> "1" [] d = 2 -> "2" [] d = 3 -> "3"
              [] d = 4 -> "4" [] d = 5 -> "5" [] d = 6 -> "6" [] d = 7 -> "7"
              [] d = 8 -> "8" [] d = 9 -> "9"

RECURSIVE IntToStr(_)
IntToStr(k) == IF k < 10 THEN Digit(k)
               ELSE IntToStr(k \div 10) \o Digit(k % 10)

VARIABLES intRet, strRet, pc, stack, a, b, n, x, s

vars == << intRet, strRet, pc, stack, a, b, n, x, s >>

ProcSet == {1}

Init == /\ intRet = 0
        /\ strRet = ""
        (* Procedure Add *)
        /\ a = [self \in ProcSet |-> 0]
        /\ b = [self \in ProcSet |-> 0]
        (* Procedure ToString *)
        /\ n = [self \in ProcSet |-> 0]
        (* Process Main *)
        /\ x = [self \in ProcSet |-> 0]
        /\ s = [self \in ProcSet |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Start"]

AddLbl(self) == /\ pc[self] = "AddLbl"
                /\ intRet' = a[self] + b[self]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
                /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << strRet, n, x, s >>

Add(self) == AddLbl(self)

StrLbl(self) == /\ pc[self] = "StrLbl"
                /\ Assert(n[self] = 10,
                          "Failure of assertion: n passed to ToString must be 10")
                /\ strRet' = IntToStr(n[self])
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << intRet, a, b, x, s >>

ToString(self) == StrLbl(self)

Start(self) == /\ pc[self] = "Start"
               /\ /\ a' = [a EXCEPT ![self] = 4]
                  /\ b' = [b EXCEPT ![self] = 6]
                  /\ stack' = [stack EXCEPT ![self] =
                                  << [ procedure |-> "Add",
                                       pc        |-> "SaveX",
                                       a         |-> a[self],
                                       b         |-> b[self] ] >>
                                  \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "AddLbl"]
               /\ UNCHANGED << intRet, strRet, n, x, s >>

SaveX(self) == /\ pc[self] = "SaveX"
               /\ x' = [x EXCEPT ![self] = intRet]
               /\ /\ n' = [n EXCEPT ![self] = x'[self]]
                  /\ stack' = [stack EXCEPT ![self] =
                                  << [ procedure |-> "ToString",
                                       pc        |-> "Finish",
                                       n         |-> n[self] ] >>
                                  \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "StrLbl"]
               /\ UNCHANGED << intRet, strRet, a, b, s >>

Finish(self) == /\ pc[self] = "Finish"
                /\ s' = [s EXCEPT ![self] = strRet]
                /\ Assert(s'[self] = "10",
                          "Failure of assertion: final output must be \"10\"")
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << intRet, strRet, stack, a, b, n, x >>

Main(self) == Start(self) \/ SaveX(self) \/ Finish(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : Add(self) \/ ToString(self))
           \/ Main(1)
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Main(1)) /\ WF_vars(Add(1)) /\ WF_vars(ToString(1))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ intRet \in Nat
          /\ strRet \in {"", "10"}
          /\ pc \in [ProcSet -> {"Start", "AddLbl", "SaveX", "StrLbl",
                                 "Finish", "Done"}]
          /\ a \in [ProcSet -> Nat]
          /\ b \in [ProcSet -> Nat]
          /\ n \in [ProcSet -> Nat]
          /\ x \in [ProcSet -> Nat]
          /\ s \in [ProcSet -> {"", "10"}]
          /\ \A self \in ProcSet : Len(stack[self]) <= 1

ToStringArgIs10 == \A self \in ProcSet : pc[self] = "StrLbl" => n[self] = 10

OutputIs10 == \A self \in ProcSet : pc[self] = "Done" => s[self] = "10"

StackConsistent ==
    \A self \in ProcSet :
        /\ pc[self] \in {"AddLbl", "StrLbl"} <=> stack[self] /= << >>
        /\ pc[self] = "AddLbl" => Head(stack[self]).procedure = "Add"
        /\ pc[self] = "StrLbl" => Head(stack[self]).procedure = "ToString"

-----------------------------------------------------------------------------
(* Liveness / progress properties *)

AddEventuallyReturns ==
    \A self \in ProcSet : (pc[self] = "AddLbl") ~> (pc[self] = "SaveX")

ToStringEventuallyReturns ==
    \A self \in ProcSet : (pc[self] = "StrLbl") ~> (pc[self] = "Finish")

EventuallyOutput10 == <>(\A self \in ProcSet : s[self] = "10")

StartLeadsToDone ==
    \A self \in ProcSet : (pc[self] = "Start") ~> (pc[self] = "Done")

=============================================================================