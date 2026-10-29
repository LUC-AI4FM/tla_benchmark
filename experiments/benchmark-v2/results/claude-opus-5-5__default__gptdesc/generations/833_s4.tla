```tla
teBefore(order, OrderPos(order, c))

-----------------------------------------------------------------------------
(* Liveness *)

\* Every client request is eventually observed as acknowledged.
\* (Together with deadlock checking: no state other than one in which all
\*  requests are acknowledged may lack an enabled step.)
AllRequestsObserved == <>AllAcked

=============================================================================
```