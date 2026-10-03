---- MODULE ProcCall ----
EXTENDS Integers, Strings, Sequences, TLC

CONSTANT Procs
ASSUME Procs = {"p1"}

VARIABLES
    pc,      \* The program counter for each process
    stack,   \* The call stack for each process
    sum,     \* Local variable for the main process
    output,  \* Local variable for the main process
    a, b, res, \* Parameters and local for Addition procedure
    n, s     \* Parameter and local for IntToString procedure

vars == <<pc, stack, sum, output, a, b, res, n, s>>

P1 == CHOOSE p \in Procs : TRUE

\* Main process actions
P_start(self) ==
    /\ pc[self] = "P_start"
    /\ pc' = [pc EXCEPT ![self] = "P_call_add"]
    /\ UNCHANGED <<stack, sum, output, a, b, res, n, s>>

P_call_add(self) ==
    /\ pc[self] = "P_call_add"
    /\ a' = [a EXCEPT ![self] = 3]
    /\ b' = [b EXCEPT ![self] = 7]
    /\ stack' = [stack EXCEPT ![self] = <<[pc |-> "P_after_add"]>>]
    /\ pc' = [pc EXCEPT ![self] = "Add_start"]
    /\ UNCHANGED <<sum, output, res, n, s>>

P_after_add(self) ==
    /\ pc[self] = "P_after_add"
    /\ sum' = [sum EXCEPT ![self] = res[self]]
    /\ pc' = [pc EXCEPT ![self] = "P_call_istr"]
    /\ UNCHANGED <<stack, output, a, b, res, n, s>>

P_call_istr(self) ==
    /\ pc[self] = "P_call_istr"
    /\ n' = [n EXCEPT ![self] = sum[self]]
    /\ stack' = [stack EXCEPT ![self] = Append(stack[self], <<[pc |-> "P_after_istr"]>>)]
    /\ pc' = [pc EXCEPT ![self] = "IStr_start"]
    /\ UNCHANGED <<sum, output, a, b, res, s>>

P_after_istr(self) ==
    /\ pc[self] = "P_after_istr"
    /\ LET new_output == s[self]
       IN /\ output' = [output EXCEPT ![self] = new_output]
          /\ Assert(new_output = "10", "Assertion failed: final output is not '10'")
    /\ pc' = [pc EXCEPT ![self] = "P_done"]
    /\ UNCHANGED <<stack, sum, a, b, res, n, s>>

\* Addition procedure actions
Add_start(self) ==
    /\ pc[self] = "Add_start"
    /\ res' = [res EXCEPT ![self] = a[self] + b[self]]
    /\ pc' = [pc EXCEPT ![self] = "Add_return"]
    /\ UNCHANGED <<stack, sum, output, a, b, n, s>>

Add_return(self) ==
    /\ pc[self] = "Add_return"
    /\ LET frame == Head(stack[self])
       IN pc' = [pc EXCEPT ![self] = frame.pc]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED <<sum, output, a, b, res, n, s>>

\* IntToString procedure actions
IStr_start(self) ==
    /\ pc[self] = "IStr_start"
    /\ Assert(n[self] = 10, "Assertion failed: integer passed to string conversion is not 10")
    /\ s' = [s EXCEPT ![self] = ToString(n[self])]
    /\ pc' = [pc EXCEPT ![self] = "IStr_return"]
    /\ UNCHANGED <<stack, sum, output, a, b, res, n>>

IStr_return(self) ==
    /\ pc[self] = "IStr_return"
    /\ LET frame == Head(stack[self])
       IN pc' = [pc EXCEPT ![self] = frame.pc]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED <<sum, output, a, b, res, n, s>>

\* The single process is the disjunction of its possible steps.
Process(self) ==
    \/ P_start(self)
    \/ P_call_add(self)
    \/ P_after_add(self)
    \/ P_call_istr(self)
    \/ P_after_istr(self)
    \/ Add_start(self)
    \/ Add_return(self)
    \/ IStr_start(self)
    \/ IStr_return(self)

\* The system's next-state relation.
Next == Process(P1)

\* Initial state of the system.
Init ==
    /\ pc = [self \in Procs |-> "P_start"]
    /\ stack = [self \in Procs |-> <<>>]
    /\ sum = [self \in Procs |-> 0]
    /\ output = [self \in Procs |-> ""]
    /\ a = [self \in Procs |-> 0]
    /\ b = [self \in Procs |-> 0]
    /\ res = [self \in Procs |-> 0]
    /\ n = [self \in Procs |-> 0]
    /\ s = [self \in Procs |-> ""]

\* Fairness condition for the single process.
Fairness == WF_vars(Next)

\* The complete specification.
Spec == Init /\ [][Next]_vars /\ Fairness

\* --- Properties ---

\* A type invariant for the state variables.
PCValues == {"P_start", "P_call_add", "P_after_add", "P_call_istr", "P_after_istr",
             "Add_start", "Add_return", "IStr_start", "IStr_return", "P_done"}
TypeOK ==
    /\ pc \in [Procs -> PCValues]
    /\ stack \in [Procs -> Seq([pc: PCValues])]
    /\ sum \in [Procs -> Int]
    /\ output \in [Procs -> String]
    /\ a \in [Procs -> Int]
    /\ b \in [Procs -> Int]
    /\ res \in [Procs -> Int]
    /\ n \in [Procs -> Int]
    /\ s \in [Procs -> String]

\* Safety invariant: The integer passed to IntToString is correct.
CorrectInputToIntToString ==
    pc[P1] = "IStr_start" => n[P1] = 10

\* Safety invariant: The final output string is correct.
CorrectFinalOutput ==
    pc[P1] = "P_done" => output[P1] = "10"

\* Liveness property: The program eventually terminates.
Termination == <>(pc[P1] = "P_done")

=============================================================================