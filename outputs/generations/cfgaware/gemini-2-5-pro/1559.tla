---- MODULE LockHS ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Procs
ASSUME Procs = {0, 1}

Nil == CHOOSE v : v \notin Procs

(***************************************************************************)
(* This is the high-level, abstract specification of a simple lock.        *)
(* A process can acquire the lock if it's free, and release it if it holds *)
(* it. The actions are atomic.                                             *)
(***************************************************************************)
VARIABLES lock_abs
vars_abs == <<lock_abs>>

Init_abs == lock_abs = Nil

Acquire_abs(p) ==
    /\ lock_abs = Nil
    /\ lock_abs' = p

Release_abs(p) ==
    /\ lock_abs = p
    /\ lock_abs' = Nil

Next_abs == \E p \in Procs : Acquire_abs(p) \/ Release_abs(p)

Spec == Init_abs /\ [][Next_abs]_vars_abs

(***************************************************************************)
(* This is the more concrete specification that is meant to be refined by  *)
(* Peterson's algorithm. It introduces a stuttering variable `s` to break  *)
(* the atomic lock acquisition into three steps, and a history variable    *)
(* `h_turn` to record the sequence of writes to the `turn` variable.       *)
(***************************************************************************)
VARIABLES lock, h_turn, s
vars == <<lock, h_turn, s>>

InitHS ==
  /\ lock = Nil
  /\ h_turn = <<>>
  /\ s = [p \in Procs |-> 0]

(* Step 1 of entry protocol: Process p indicates interest. *)
Step1(p) ==
    /\ s[p] = 0
    /\ s' = [s EXCEPT ![p] = 1]
    /\ UNCHANGED <<lock, h_turn>>

(* Step 2 of entry protocol: Process p sets the turn. *)
Step2(p) ==
    /\ s[p] = 1
    /\ s' = [s EXCEPT ![p] = 2]
    /\ h_turn' = Append(h_turn, p)
    /\ UNCHANGED <<lock>>

(* Step 3 of entry protocol: Process p acquires the lock. *)
Acquire(p) ==
    /\ s[p] = 2
    /\ lock = Nil
    /\ s' = [s EXCEPT ![p] = 3]
    /\ lock' = p
    /\ UNCHANGED <<h_turn>>

(* Process p releases the lock. *)
Release(p) ==
    /\ lock = p
    /\ s' = [s EXCEPT ![p] = 0]
    /\ lock' = Nil
    /\ UNCHANGED <<h_turn>>

NextHS == \E p \in Procs :
            \/ Step1(p)
            \/ Step2(p)
            \/ Acquire(p)
            \/ Release(p)

SpecHS == InitHS /\ [][NextHS]_vars

(***************************************************************************)
(* Invariants for the concrete specification.                              *)
(***************************************************************************)
TypeOKHS ==
  /\ lock \in (Procs \cup {Nil})
  /\ h_turn \in Seq(Procs)
  /\ s \in [Procs -> 0..3]

(* Mutual exclusion: at most one process is in the critical section (s[p]=3). *)
LockInv == \A i, j \in Procs : i # j => ~(s[i] = 3 /\ s[j] = 3)

(* General invariant for the concrete specification. *)
InvHS ==
    /\ TypeOKHS
    /\ LockInv
    /\ (lock # Nil <=> \E p \in Procs : s[p] = 3)

(***************************************************************************)
(* Refinement mapping to Peterson's algorithm. This section defines the    *)
(* Peterson algorithm and instantiates its specification with variables    *)
(* from the concrete LockHS spec.                                          *)
(***************************************************************************)

LOCAL MODULE Peterson
    CONSTANT Procs
    ASSUME Procs = {0, 1}
    Other(p) == IF p = 0 THEN 1 ELSE 0

    VARIABLES flag, turn
    vars == <<flag, turn>>

    Init ==
        /\ flag = [p \in Procs |-> FALSE]
        /\ turn \in Procs

    (* Action for p to set its flag, indicating interest. *)
    SetFlag(p) ==
        /\ flag' = [flag EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<turn>>

    (* Action for p to set the turn variable, yielding priority. *)
    SetTurn(p) ==
        /\ turn' = p
        /\ UNCHANGED <<flag>>

    (* Stuttering step for p to enter the critical section.
       This is enabled only when the Peterson condition is met. *)
    Enter(p) ==
        /\ \/ ~flag[Other(p)]
           \/ turn # p
        /\ UNCHANGED vars

    (* Action for p to exit the critical section by resetting its flag. *)
    ResetFlag(p) ==
        /\ flag' = [flag EXCEPT ![p] = FALSE]
        /\ UNCHANGED <<turn>>

    Next == \E p \in Procs :
              \/ SetFlag(p)
              \/ SetTurn(p)
              \/ Enter(p)
              \/ ResetFlag(p)

    Spec == Init /\ [][Next]_vars
END MODULE

(* Refinement mapping functions from LockHS state to Peterson state. *)
pflag == [p \in Procs |-> s[p] > 0]
pturn == IF Len(h_turn) = 0 THEN 0 ELSE h_turn[Len(h_turn)]

(* Instantiate the Peterson specification with the mapped variables. *)
P == INSTANCE Peterson WITH flag <- pflag, turn <- pturn

PSpec == P!Spec

====