---------------------------- MODULE EnabledInstance ----------------------------
EXTENDS Naturals

-------------------------------- MODULE Inner --------------------------------
EXTENDS Naturals

VARIABLES u, v

IInit == u = 0 /\ v = 0

INext == /\ u' = 1 - u
         /\ v' = 1 - v

ISpec == IInit /\ [][INext]_<<u, v>>

(* Must hold under the substitution u <- x, v <- x:                         *)
(* ENABLED (x' = 1 - x) is TRUE in every state.                             *)
EnabledOK == ENABLED (u' = 1 - v)

(* Must NOT hold under the substitution u <- x, v <- x:                     *)
(* ENABLED (x' # x') is FALSE, because u' and v' are the same variable.     *)
EnabledBad == ENABLED (u' # v')

(* Further ENABLED-based conditions to be imported.                         *)
NextEnabled == ENABLED INext

ITypeOK == u \in {0, 1} /\ v \in {0, 1}

ISafety == [](u = v)

ISafetyEnabled == [](ENABLED INext)

ILiveness == /\ []<>(u = 1)
             /\ []<>(u = 0)
             /\ []<>(ENABLED (u' = 1 - v))
=============================================================================