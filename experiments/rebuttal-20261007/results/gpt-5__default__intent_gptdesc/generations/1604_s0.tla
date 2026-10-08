----------------------------- MODULE ProgramCallStack -----------------------------

EXTENDS Integers, Sequences

CONSTANTS A1, A2, ExpectedStr, None

(*
  A1, A2 are integer immediates passed to the adder.
  ExpectedStr is the expected string result of stringifying A1 + A2.
  None is a distinguished value used for uninitialized variables.
*)

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
  pc,           \* program counter (control location)
  stack,        \* runtime call stack (sequence of frames)
  m_sum,        \* main's local to hold the integer result from Add
  m_str,        \* main's local to hold the string result from Stringify
  Out,          \* global output string
  add_arg1, add_arg2, add_ret,    \* adder parameters and return value
  str_arg, str_ret,               \* stringify parameter and return value
  Error         \* becomes TRUE on an assertion failure
  

vars == << pc, stack, m_sum, m_str, Out, add_arg1, add_arg2, add_ret, str_arg, str_ret, Error >>

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

PCs == {
  "Main_Init", "Main_AfterAdd", "Main_AfterStr",
  "Add_Begin", "Add_Return",
  "Str_Begin", "Str_Return",
  "Main_Assert",
  "Done", "Error"
}

ReturnPCs == { "Main_AfterAdd", "Main_AfterStr" }

MaybeInt == Int \cup { None }
MaybeStr == { ExpectedStr } \cup { None }

FrameType == [ retpc: ReturnPCs,
               saved: [ m_sum: MaybeInt, m_str: MaybeStr, out: MaybeStr ] ]

IsEmpty(s) == Len(s) = 0
Top(s) == s[Len(s)]
Pop(s) == SubSeq(s, 1, Len(s)-1)

Sum == A1 + A2

Terminated == /\ pc = "Done"
              /\ Len(stack) = 0

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ A1 \in Int /\ A2 \in Int
  /\ pc = "Main_Init"
  /\ stack = << >>
  /\ m_sum = None
  /\ m_str = None
  /\ Out = None
  /\ add_arg1 = None
  /\ add_arg2 = None
  /\ add_ret  = None
  /\ str_arg  = None
  /\ str_ret  = None
  /\ Error = FALSE

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

MainCallAdd ==
  /\ pc = "Main_Init"
  /\ IsEmpty(stack)
  /\ stack' = stack \o << [ retpc |-> "Main_AfterAdd",
                             saved |-> [ m_sum |-> m_sum,
                                         m_str |-> m_str,
                                         out   |-> Out ] ] >>
  /\ add_arg1' = A1
  /\ add_arg2' = A2
  /\ pc' = "Add_Begin"
  /\ UNCHANGED << add_ret, str_arg, str_ret, m_sum, m_str, Out, Error >>

AddCompute ==
  /\ pc = "Add_Begin"
  /\ add_ret' = add_arg1 + add_arg2
  /\ pc' = "Add_Return"
  /\ UNCHANGED << stack, add_arg1, add_arg2, str_arg, str_ret, m_sum, m_str, Out, Error >>

ReturnFromAdd ==
  /\ pc = "Add_Return"
  /\ Len(stack) > 0
  /\ Top(stack).retpc = "Main_AfterAdd"
  /\ LET fr == Top(stack) IN
       /\ stack' = Pop(stack)
       /\ m_sum' = add_ret
       /\ m_str' = fr.saved.m_str
       /\ Out'   = fr.saved.out
       /\ pc'    = fr.retpc
  /\ UNCHANGED << add_arg1, add_arg2, add_ret, str_arg, str_ret, Error >>

MainCallStr ==
  /\ pc = "Main_AfterAdd"
  /\ stack' = stack \o << [ retpc |-> "Main_AfterStr",
                             saved |-> [ m_sum |-> m_sum,
                                         m_str |-> m_str,
                                         out   |-> Out ] ] >>
  /\ str_arg' = m_sum
  /\ pc' = "Str_Begin"
  /\ UNCHANGED << add_arg1, add_arg2, add_ret, str_ret, m_sum, m_str, Out, Error >>

StrCompute ==
  /\ pc = "Str_Begin"
  /\ str_arg = Sum
  /\ str_ret' = ExpectedStr
  /\ pc' = "Str_Return"
  /\ UNCHANGED << stack, add_arg1, add_arg2, add_ret, str_arg, m_sum, m_str, Out, Error >>

StrFail ==
  /\ pc = "Str_Begin"
  /\ str_arg # Sum
  /\ pc' = "Error"
  /\ Error' = TRUE
  /\ UNCHANGED << stack, add_arg1, add_arg2, add_ret, str_arg, str_ret, m_sum, m_str, Out >>

ReturnFromStr ==
  /\ pc = "Str_Return"
  /\ Len(stack) > 0
  /\ Top(stack).retpc = "Main_AfterStr"
  /\ LET fr == Top(stack) IN
       /\ stack' = Pop(stack)
       /\ m_sum' = fr.saved.m_sum
       /\ m_str' = str_ret
       /\ Out'   = str_ret
       /\ pc'    = fr.retpc
  /\ UNCHANGED << add_arg1, add_arg2, add_ret, str_arg, str_ret, Error >>

MainAssertPass ==
  /\ pc = "Main_AfterStr"
  /\ Out = ExpectedStr
  /\ pc' = "Done"
  /\ UNCHANGED << stack, add_arg1, add_arg2, add_ret, str_arg, str_ret, m_sum, m_str, Out, Error >>

MainAssertFail ==
  /\ pc = "Main_AfterStr"
  /\ Out # ExpectedStr
  /\ pc' = "Error"
  /\ Error' = TRUE
  /\ UNCHANGED << stack, add_arg1, add_arg2, add_ret, str_arg, str_ret, m_sum, m_str, Out >>

Next ==
  MainCallAdd
  \/ AddCompute
  \/ ReturnFromAdd
  \/ MainCallStr
  \/ StrCompute
  \/ StrFail
  \/ ReturnFromStr
  \/ MainAssertPass
  \/ MainAssertFail

(***************************************************************************)
(* Fairness: each enabled action cannot be indefinitely postponed          *)
(***************************************************************************)

Fairness ==
  /\ WF_vars(MainCallAdd)
  /\ WF_vars(AddCompute)
  /\ WF_vars(ReturnFromAdd)
  /\ WF_vars(MainCallStr)
  /\ WF_vars(StrCompute)
  /\ WF_vars(ReturnFromStr)
  /\ WF_vars(MainAssertPass)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Invariants and properties                                               *)
(***************************************************************************)

TypeOK ==
  /\ pc \in PCs
  /\ stack \in Seq(FrameType)
  /\ m_sum \in MaybeInt
  /\ m_str \in MaybeStr
  /\ Out   \in MaybeStr
  /\ add_arg1 \in MaybeInt
  /\ add_arg2 \in MaybeInt
  /\ add_ret  \in MaybeInt
  /\ str_arg  \in MaybeInt
  /\ str_ret  \in MaybeStr
  /\ Error \in BOOLEAN

SafetyOut ==
  [](pc = "Done" => Out = ExpectedStr)

Termination ==
  <> Terminated

THEOREM Spec => []TypeOK
THEOREM Spec => SafetyOut
THEOREM Spec => Termination

================================================================================