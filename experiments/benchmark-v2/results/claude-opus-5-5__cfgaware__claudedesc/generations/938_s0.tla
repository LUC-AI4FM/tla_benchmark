---------------------- MODULE LiveInternalMemory ----------------------
EXTENDS InternalMemory

Liveness2 == \A p \in Proc : WF_<<memInt, mem, ctl, buf>>(Do(p) \/ Rsp(p))

Liveness == \A p \in Proc : /\ WF_<<memInt, mem, ctl, buf>>(Do(p))
                            /\ WF_<<memInt, mem, ctl, buf>>(Rsp(p))

LISpec == ISpec /\ Liveness2

LivenessProperty == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

THEOREM LISpec => LivenessProperty
=============================================================================