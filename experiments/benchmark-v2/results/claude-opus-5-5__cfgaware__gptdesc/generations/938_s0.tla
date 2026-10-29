------------------------ MODULE LiveInternalMemory ------------------------
EXTENDS InternalMemory

vmem == <<mem, ctl, buf>>

Liveness == \A p \in Proc : WF_vmem(Do(p)) /\ WF_vmem(Rsp(p))

Liveness2 == \A p \in Proc : WF_vmem(Do(p) \/ Rsp(p))

LISpec == ISpec /\ Liveness2

LivenessProperty == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "ready")

THEOREM LISpec => LivenessProperty
=============================================================================