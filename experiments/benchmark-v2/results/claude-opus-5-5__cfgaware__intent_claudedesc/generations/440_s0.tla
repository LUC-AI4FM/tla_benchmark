------------------------------ MODULE EnabledInstance ------------------------------
EXTENDS Naturals

  ---------------------------- MODULE Inner ----------------------------
  VARIABLES u, v

  IInit == u \in {0, 1} /\ v \in {0, 1} /\ u = v

  INext == /\ u' = 1 - u
           /\ v' = 1 - v

  \* Holds under the substitution u <- x, v <- x, because the conjuncts
  \* become x' = 1 - x /\ x' = 1 - x, which is satisfiable.
  EnabledTrue == ENABLED (u' = 1 - u /\ v' = 1 - v)

  \* Holds in Inner itself, but must NOT hold under the substitution:
  \* the conjuncts become x' = x /\ x' = 1 - x, which is unsatisfiable.
  EnabledFalse == ENABLED (u' = u /\ v' = 1 - v)

  ISafety == [](u = v)

  ISafetyEnabled == [](ENABLED (u' = 1 - u /\ v' = 1 - v))

  ILiveness == /\ []<>(u = 0)
               /\ []<>(u = 1)
               /\ []<>(v = 0)
               /\ []<>(v = 1)

  ILivenessEnabled == []<>(ENABLED INext)

  ISpec == IInit /\ [][INext]_<<u, v>> /\ WF_<<u, v>>(INext)
  ======================================================================