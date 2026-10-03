---------------- MODULE EvenOdd ----------------

EXTENDS Naturals, Sequences, TLC

CONSTANT N
ASSUME N \in Nat

VARIABLES pc, stack, xEven, xOdd, result

vars == << pc, stack, xEven, xOdd, result >>

(* The set of all possible program counter values. *)
PC_Values == {"L_main", "E1", "O1", "E_ret", "O_ret", "SetResult", "Done"}

(*
--algorithm EvenOdd
variables
  res = FALSE;

procedure Even(x)
begin E:
  if x = 0 then
    return TRUE;
  else
    return Odd(x-1);
  end if;
end procedure;

procedure Odd(x)
begin O:
  if x = 0 then
    return FALSE;
  else
    return Even(x-1);
  end if;
end procedure;

begin
  res := Even(N);
end algorithm;
*)

TypeOK ==
    /\ pc \in PC_Values
    /\ stack \in Seq(PC_Values)
    /\ xEven \in Nat
    /\ xOdd \in Nat
    /\ result \in BOOLEAN

Init ==
    /\ pc = "L_main"
    /\ stack = <<>>
    /\ xEven = 0
    /\ xOdd = 0
    /\ result = FALSE

(* Main algorithm body: Call Even(N) *)
L_main ==
    /\ pc = "L_main"
    /\ pc' = "E1"
    /\ xEven' = N
    /\ stack' = << "SetResult" >>
    /\ UNCHANGED <<xOdd, result>>

(* Procedure Even(xEven) *)
EvenProc ==
    /\ pc = "E1"
    /\ IF xEven = 0
       THEN (* Base case: return TRUE *)
            /\ pc' = Head(stack)
            /\ stack' = Tail(stack)
            /\ result' = TRUE
            /\ UNCHANGED <<xEven, xOdd>>
       ELSE (* Recursive step: call Odd(xEven - 1) *)
            /\ pc' = "O1"
            /\ xOdd' = xEven - 1
            /\ stack' = Append(stack, "E_ret")
            /\ UNCHANGED <<xEven, result>>

(* Procedure Odd(xOdd) *)
OddProc ==
    /\ pc = "O1"
    /\ IF xOdd = 0
       THEN (* Base case: return FALSE *)
            /\ pc' = Head(stack)
            /\ stack' = Tail(stack)
            /\ result' = FALSE
            /\ UNCHANGED <<xEven, xOdd>>
       ELSE (* Recursive step: call Even(xOdd - 1) *)
            /\ pc' = "E1"
            /\ xEven' = xOdd - 1
            /\ stack' = Append(stack, "O_ret")
            /\ UNCHANGED <<xOdd, result>>

(* Return from Even procedure. The return value is already in 'result'. *)
EvenReturn ==
    /\ pc = "E_ret"
    /\ pc' = Head(stack)
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<xEven, xOdd, result>>

(* Return from Odd procedure. The return value is already in 'result'. *)
OddReturn ==
    /\ pc = "O_ret"
    /\ pc' = Head(stack)
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<xEven, xOdd, result>>

(* The initial call has returned. The final answer is in 'result'. Move to Done. *)
SetResultAction ==
    /\ pc = "SetResult"
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, xEven, xOdd, result>>

(* The algorithm has terminated. Stutter to prevent deadlock. *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ L_main
    \/ EvenProc
    \/ OddProc
    \/ EvenReturn
    \/ OddReturn
    \/ SetResultAction
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

THEOREM Spec => []TypeOK
THEOREM Spec => Termination

=============================================================================