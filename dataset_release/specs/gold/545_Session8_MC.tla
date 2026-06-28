---- MODULE Session8_MC ----
\* EXTENDS Session8alt
\* EXTENDS Session8onebit
EXTENDS Session8peterson

ConstN == 3
ConstProcs == 0..(ConstN-1)

MutualExclusion == \A p, q \in Procs:
                    (p /= q) => ~((pc[p] = "cs") /\ (pc[q] = "cs"))

====
