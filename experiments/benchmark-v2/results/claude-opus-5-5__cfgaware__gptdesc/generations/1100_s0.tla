---------------------------- MODULE AbstractLock ----------------------------
EXTENDS Naturals, TLC

Procs == {1, 2}

(* --algorithm AbstractLock
variables lock = TRUE;

fair+ process P \in Procs
begin
ncs:
  while TRUE do
    skip;
l1:
    await lock;
    lock := FALSE;
cs:
    skip;
l2:
    lock := TRUE;
  end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ lock = TRUE
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock
            /\ lock' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in Procs: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : SF_vars(P(self))

\* END TRANSLATION

TypeOK == /\ lock \in BOOLEAN
          /\ pc \in [ProcSet -> {"ncs", "l1", "cs", "l2"}]

LockInv == /\ \A i, j \in ProcSet :
                 (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")
           /\ (~lock) <=> (\E p \in ProcSet : pc[p] \in {"cs", "l2"})

Liveness == (pc[1] = "l1") ~> (pc[1] = "cs")

=============================================================================