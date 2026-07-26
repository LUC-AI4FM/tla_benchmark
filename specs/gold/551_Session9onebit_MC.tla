---- MODULE Session9onebit_MC ----
EXTENDS Session9onebit

ConstN == 3
ConstProcs == 0..(ConstN-1)

MutualExclusion == \A p, q \in Procs:
                    (p /= q) => ~((pc[p] = "cs") /\ (pc[q] = "cs"))

DeadAndLivelockFree == (\E i \in Procs: pc[i] = "enter") ~> (\E i \in Procs: pc[i] = "cs")

NoStarveProc0 == (pc[0] = "enter") ~> (pc[0] = "cs")
NoStarveProc1 == (pc[1] = "enter") ~> (pc[1] = "cs")    \* Not satisfied by this algorithm

====
