------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, Integers

CONSTANT MaxNum \in Nat

(* Program counter constants *)
CONSTANT InitPC, LoopPC, EndPC

VARIABLES u_ini, v_ini, u, v, pc

(* Mathematical GCD function (recursive) *)
GCD(a,b) == IF b = 0 THEN a ELSE GCD(b, a % b)

(* Predicate to ensure numbers are in the allowed range *)
ValidRange(x) == 1 <= x /\ x <= MaxNum

vars == <<u_ini, v_ini, u, v, pc>>

Init ==
    /\ u_ini \in Nat
    /\ v_ini \in Nat
    /\ ValidRange(u_ini)
    /\ ValidRange(v_ini)
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = InitPC

Next ==
  CASE 
      pc = InitPC ->
          /\ pc' = LoopPC
          /\ UNCHANGED <<u, v>>
      
      pc = LoopPC /\ v > 0 ->
          LET r == u % v IN
              /\ pc' = LoopPC
              /\ u' = v
              /\ v' = r
      
      pc = LoopPC /\ v = 0 ->
          /\ pc' = EndPC
          /\ UNCHANGED <<u, v>>
      
      pc = EndPC -> pc' = EndPC
  ENDCASE

Safety ==
    (* Correctness invariant: when the algorithm terminates, u equals the GCD of the initial values *)
    (pc = EndPC => GCD(u_ini, v_ini) = u)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Safety

=============================================================================