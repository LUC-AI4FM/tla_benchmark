------------------------------ MODULE DequeSpec ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Val, defaultInitValue, MaxNodes

(* ------------------------------------------------------------------ *)
(* Type definitions *)

SUBSET Addr \subseteq 0..MaxNodes-1
Node == [prev:Addr, next:Addr, val:Val]

(* ------------------------------------------------------------------ *)
(* Variables *)

VARIABLES head, tail, nodes, freeList, status

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
  /\ head = defaultInitValue
  /\ tail = defaultInitValue
  /\ nodes =
        [i \in Addr |-> IF i = defaultInitValue THEN
                           [prev |-> defaultInitValue,
                            next |-> defaultInitValue,
                            val |-> "sentinel"]
                         ELSE
                           [prev |-> defaultInitValue,
                            next |-> defaultInitValue,
                            val |-> "null"]]
  /\ freeList = {i \in Addr : i # defaultInitValue}
  /\ status = ""

(* ------------------------------------------------------------------ *)
(* Push Left operation *)

PushLeft ==
  /\ freeList # {}
  /\ f \in free