---------------------------- MODULE InstanceUnchangedConst ----------------------------
(***************************************************************************)
(* Shows that a constant-valued operator substituted for a variable via an *)
(* INSTANCE ... WITH clause is handled correctly, including inside an      *)
(* UNCHANGED expression.                                                   *)
(*                                                                         *)
(* The instantiated module Inner has three variables p, q and r. The main  *)
(* module substitutes its variables x and y for p and q. It substitutes    *)
(* the constant-valued operator C for r. Inside Inner!Next the expression  *)
(* UNCHANGED <<q, r>> becomes UNCHANGED <<y, C>>, that is y' = y /\ C' = C. *)
(* Because C is a constant, C' = C is trivially TRUE. TLC must evaluate it *)
(* without crashing and without reporting C as undefined.                  *)
(*                                                                         *)
(* Model check with deadlock checking disabled. The expected result is no  *)
(* errors.                                                                 *)
(***************************************************************************)
EXTENDS Naturals

  ---------------------------- MODULE Inner ----------------------------
  VARIABLES p, q, r

  Vals == {0, 1}

  InnerInit == /\ p \in Vals
               /\ q \in Vals
               /\ r \in Vals

  \* Increment p (bounded so that the state space is finite), and leave
  \* q and r unchanged.
  InnerNext == /\ p' = (p + 1) % 3
               /\ UNCHANGED <<q, r>>

  InnerSpec == InnerInit /\ [][InnerNext]_<<p, q, r>>

  InnerTypeOK == /\ p \in 0..2
                 /\ q \in Vals
                 /\ r \in Vals
  ======================================================================