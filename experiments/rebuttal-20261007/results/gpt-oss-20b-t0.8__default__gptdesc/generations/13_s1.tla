--------------------------- MODULE RollingDeployment ----------------------------
EXTENDS Naturals, TLC

CONSTANTS SERVERS \* set of server identifiers (e.g., 1..N)
CONSTANT NULL   \* sentinel value not in SERVERS

VARIABLES st, inLB, phase, curr

(* Types *)
ServerState == {"ok", "updating", "updated"}
Phase       == {"idle","waiting"}

(* Initial state: all servers ok and in LB; no server removed; phase idle *)
Init ==
  /\ st \in [SERVERS -> ServerState]
  /\ inLB \in [SERVERS -> BOOLEAN]
  /\ phase \in Phase
  /\ curr \in SERVERS \/ {NULL}
  /\ ∀ s ∈ SERVERS :
        /\ st[s] = "ok"
        /\ inLB[s] = TRUE
  /\ phase = "idle"
  /\ curr = NULL

(* Per-server start update *)
PerServerStart ==
  ∃ s ∈ SERVERS :
    /\ st[s] = "ok"
    /\ NOT inLB[s]
    /\ st' = [st EXCEPT ![s] = "updating"]
    /\ inLB' = inLB
    /\ phase' = phase
    /\ curr' = curr

(* Per-server finish update *)
PerServerFinish ==
  ∃ s ∈ SERVERS :
    /\ st[s] = "updating"
    /\ st' = [st EXCEPT ![s] = "updated"]
    /\ inLB' = inLB
    /\ phase' = phase
    /\ curr' = curr

(* Coordinator removes a server from LB *)
CoordinatorRemove ==
  /\ phase = "idle"
  /\ ∃ s ∈ SERVERS : st[s] = "ok" /\ inLB[s]
  LET s0 == CHOOSE s ∈ SERVERS : st[s] = "ok" /\ inLB[s] IN
    /\ inLB' = [inLB EXCEPT ![s0] = FALSE]
    /\ curr' = s0
    /\ phase' = "waiting"
    /\ st' = st

(* Coordinator restores a server to LB *)
CoordinatorRestore ==
  /\ phase = "waiting"
  /\ curr ∈ SERVERS
  /\ st[curr] = "updated"
  /\ inLB' = [inLB EXCEPT ![curr] = TRUE]
  /\ curr' = NULL
  /\ phase' = "idle"
  /\ st' = st

Next == PerServerStart \/ PerServerFinish \/ CoordinatorRemove \/ CoordinatorRestore

vars == <<st, inLB, phase, curr>>

Fairness ==
  WF(PerServerStart) /\ WF(PerServerFinish) /\ WF(CoordinatorRemove) /\ WF(CoordinatorRestore)

Safety ==
  /\ ∀ s ∈ SERVERS : (st[s] = "updating") ⇒ NOT inLB[s]
  /\ phase ∈ Phase
  /\ curr ∈ SERVERS \/ {NULL}
  /\ (phase = "waiting") => curr ∈ SERVERS

Termination ==
  <> (∀ s ∈ SERVERS : st[s] = "updated" /\ inLB[s]) /\ (phase = "idle")

Spec == Init /\ [][Next]_vars /\ Fairness /\ Safety

THEOREM Termination_Enabled == Spec => Termination

=============================================================================