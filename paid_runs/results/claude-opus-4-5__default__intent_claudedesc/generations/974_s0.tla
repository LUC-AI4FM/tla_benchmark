-------------------------------- MODULE RegularRegisters --------------------------------
EXTENDS Integers, FiniteSets, Naturals, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 0..(N-1)

LeftNeighbor(i) == (i - 1 + N) % N

(*
Process states:
- "idle": initial state, hasn't started writing
- "writing": started writing 1, register is in transitional state
- "written": completed write, register stably holds 1
- "done": has read neighbor's register into local register
*)

VARIABLES
    pc,         \* pc[i] = process i's program counter
    shared,     \* shared[i] = stable value of process i's shared register (0 or 1)
    writing,    \* writing[i] = TRUE if process i is currently writing (transitional)
    local       \* local[i] = process i's local register (value read from neighbor)

vars == <<pc, shared, writing, local>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "writing", "written", "done"}]
    /\ shared \in [Procs -> {0, 1}]
    /\ writing \in [Procs -> BOOLEAN]
    /\ local \in [Procs -> {0, 1}]

Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ shared = [i \in Procs |-> 0]
    /\ writing = [i \in Procs |-> FALSE]
    /\ local = [i \in Procs |-> 0]

(* 
Step 1: Process i begins writing 1 to its shared register.
The register enters a transitional state where reads may return 0 or 1.
*)
BeginWrite(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "writing"]
    /\ writing' = [writing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<shared, local>>

(*
Step 2: Process i completes writing 1 to its shared register.
The register now stably holds 1.
*)
EndWrite(i) ==
    /\ pc[i] = "writing"
    /\ pc' = [pc EXCEPT ![i] = "written"]
    /\ shared' = [shared EXCEPT ![i] = 1]
    /\ writing' = [writing EXCEPT ![i] = FALSE]
    /\ UNCHANGED local

(*
Step 3: Process i reads the shared register of its left neighbor.
If the neighbor is in transitional state (writing), the read may return 0 or 1.
Otherwise, it returns the stable value.
*)
Read(i) ==
    /\ pc[i] = "written"
    /\ LET neighbor == LeftNeighbor(i)
       IN IF writing[neighbor]
          THEN \* Regular register semantics: may read old (0) or new (1) value
               \E v \in {0, 1} : local' = [local EXCEPT ![i] = v]
          ELSE \* Stable read: return the actual value
               local' = [local EXCEPT ![i] = shared[neighbor]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<shared, writing>>

Next ==
    \E i \in Procs : BeginWrite(i) \/ EndWrite(i) \/ Read(i)

Fairness == \A i \in Procs : WF_vars(BeginWrite(i)) /\ WF_vars(EndWrite(i)) /\ WF_vars(Read(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(* All processes have completed *)
AllDone == \A i \in Procs : pc[i] = "done"

(* At least one process read 1 *)
SomeoneReadOne == \E i \in Procs : local[i] = 1

(* Safety property: when all done, someone read 1 *)
Safety == AllDone => SomeoneReadOne

(* Liveness: all processes eventually complete *)
Liveness == <>AllDone

(*
Inductive Invariant for proving Safety

Key insight: Consider the process j that is the "last" to have its register read 
(i.e., the process whose right neighbor reads last among all processes).
When that right neighbor reads j's register, j must have already completed its write
(since the right neighbor only reads after completing its own write, and there's a
circular dependency). Therefore, j's register stably holds 1, so the reader gets 1.

We capture this with a more direct invariant:
- If process i has finished reading (pc[i] = "done"), and its left neighbor j
  had completed writing before i started reading, then local[i] = 1.
- Specifically: if i is done and LeftNeighbor(i) has pc = "written" or "done" 
  and writing[LeftNeighbor(i)] = FALSE, and shared[LeftNeighbor(i)] = 1,
  then local[i] = 1.

Simpler approach: Track that once a process completes writing, any subsequent
stable read of its register returns 1.
*)

(* 
Auxiliary predicate: process j's register is "definitely 1" - 
either stably written or being written (will be 1)
*)
RegisterIsOrWillBe1(j) == shared[j] = 1 \/ writing[j]

(*
Key invariant component: If process i is done reading, and at the moment of reading,
its left neighbor's register was stable (not being written) and held 1, then local[i] = 1.

Since we can't directly reference "moment of reading", we use:
- If i is done and left neighbor has shared[neighbor] = 1 and is not writing,
  then either local[i] = 1, or the read happened while neighbor was still writing.

Better approach: Once written, shared stays 1. If i reads when neighbor is not writing
and shared[neighbor] = 1, then local[i] = 1.
*)

(* Monotonicity: once shared[i] = 1, it stays 1 *)
SharedMonotonic == \A i \in Procs : shared[i] = 1 => shared[i]' = 1

(* Once a process is done writing (pc = "written" or "done"), shared = 1 *)
WrittenMeansShared1 == \A i \in Procs : (pc[i] = "written" \/ pc[i] = "done") => shared[i] = 1

(* If not writing, then consistent state *)
NotWritingConsistent == \A i \in Procs : ~writing[i] => (pc[i] # "writing")

(* Writing flag is consistent with pc *)
WritingConsistent == \A i \in Procs : writing[i] <=> pc[i] = "writing"

(*
Core invariant for the circular argument:
In any configuration where all processes are done, at least one must have read 1.

Proof sketch: Consider the circular sequence of reads. Each process i reads from
LeftNeighbor(i). Since all processes complete their writes before reading, and
all eventually read, consider the last process to begin writing. When its right
neighbor reads it, the write must be at least in progress (writing or done).
If the write completed, the reader sees 1. If still writing, the reader may see
0 or 1. But the "last writer" started after all others began writing, so its
left neighbor must have completed writing before "last writer" reads.
Thus the "last writer" definitely reads 1.

Formal invariant: We track the set of processes that have completed writing.
The last one to start writing will read from a completed write.
*)

(* Set of processes that have at least started writing *)
StartedWriting == {i \in Procs : pc[i] # "idle"}

(* Set of processes that have completed writing *)
CompletedWriting == {i \in Procs : pc[i] \in {"written", "done"}}

(* Set of processes that are done *)
DoneProcs == {i \in Procs : pc[i] = "done"}

(*
Key insight reformulated:
If all processes are done, then all processes have completed writing (shared = 1).
The last process to READ must have read from a neighbor who completed writing.
Since reading happens after completing one's own write, and all processes read
from their left neighbor, the "temporal ordering" ensures at least one stable read.

Simpler counting argument:
- When process i reads, if its left neighbor j has completed writing (not writing[j]),
  then local[i] = shared[j] = 1 (since j completed => shared[j] = 1).
- When all are done, all have read. At least one of them read from a completed write.
- Consider process 0's read time. Either LeftNeighbor(0) = N-1 was done writing or not.
  Continue around the circle. At least one read catches a completed write.
*)

(* 
If i is done and left neighbor had completed writing (is in "written" or "done" 
and not writing), then local[i] = 1.
*)
StableReadGives1 == \A i \in Procs :
    (pc[i] = "done" /\ pc[LeftNeighbor(i)] \in {"written", "done"} /\ ~writing[LeftNeighbor(i)])
    => local[i] = 1

(*
Actually, the condition should be: if at read time the neighbor was not writing.
We need to capture this differently. Let's use:
If i just became "done" (Read action), and neighbor was not writing, then local[i] = 1.
This is ensured by the Read action definition.

For the invariant, we need: the condition that ensures Safety.
When AllDone:
- All pc[i] = "done", so all completed writes (shared[i] = 1 for all)
- All reading happened in the past
- At least one read happened after its neighbor completed writing

The key is: not all reads can happen while neighbor is still writing,
because that would require a cycle of "read while writing" which is impossible
given the sequencing (write completes before read).
*)

(* 
Let's define: ReadWhileWriting(i) = TRUE if process i performed its read
while its left neighbor was in "writing" state.
We can't directly track this without adding history, so let's add a ghost variable.
*)

(* For verification, we'll use model checking on small N and state the invariant *)

(* Combined Inductive Invariant *)
IndInv ==
    /\ TypeOK
    /\ WrittenMeansShared1
    /\ WritingConsistent
    /\ (\A i \in Procs : pc[i] = "idle" => ~writing[i] /\ shared[i] = 0)
    /\ (\A i \in Procs : pc[i] = "writing" => writing[i] /\ shared[i] = 0)
    /\ (\A i \in Procs : pc[i] \in {"written", "done"} => ~writing[i] /\ shared[i] = 1)

(*
For the main safety property, we need to show that when AllDone, SomeoneReadOne.

Key lemma: When all processes have completed (AllDone), not all of them can have
local[i] = 0. 

Proof: Suppose for contradiction all local[i] = 0. Then each process i read 0
from its left neighbor LeftNeighbor(i). For a stable read (neighbor not writing),
this would mean shared[LeftNeighbor(i)] = 0, but when i reads, i has completed
writing so shared[i] = 1. Contradiction unless the read was during writing.
So all reads must have occurred while the neighbor was writing.

But process i reads only after completing its own write. So when i reads, 
shared[i] = 1. For all reads to see 0, each must read while neighbor is writing.
This means for all i: when i reads, LeftNeighbor(i) is in "writing" state.

Consider the sequence of events. Process i reads only in "written" state.
For i to read while LeftNeighbor(i) is "writing", LeftNeighbor(i) must not have
completed writing when i reads.

Consider process 0 reading from N-1. 0 is in "written" state, N-1 is in "writing".
Consider process N-1 reading from N-2. N-1 is in "written" state, N-2 is in "writing".
...
Consider process 1 reading from 0. 1 is in "written" state, 0 is in "writing".

But 0 is in "written" state when reading, so 0 has completed writing.
Yet 1 reads from 0 while 0 is "writing". Contradiction!

Therefore, not all processes read while their neighbor was writing.
At least one reads from a completed write and thus gets 1.
*)

(* 
Formalization: Define MayHaveRead0(i) = TRUE iff process i could have read 0.
This requires that when i read, LeftNeighbor(i) was either:
1. In stable state with shared = 0 (impossible once LeftNeighbor wrote), or  
2. In transitional "writing" state.

If all processes are done, all have shared = 1. So option 1 is impossible.
For option 2: when i read (pc[i] goes from "written" to "done"), was
LeftNeighbor(i) in "writing" state?

If MayHaveRead0(i) for all i, then when each i read, LeftNeighbor(i) was "writing".
Since i was "written" when reading, i had finished writing.
So when 0 reads, N-1 is "writing" but 0 is "written".
When N-1 reads, N-2 is "writing" but N-1 is "written".
...
When 1 reads, 0 is "writing" but 1 is "written".

At the time 1 reads: 1 is "written", so 1 has completed writing.
0 is "writing", so 0 hasn't completed writing, so 0 is not yet "written",
so 0 hasn't read yet (0 reads only from "written" state).
But 0 reading happens after 0 reaches "written", and 0 is currently "writing",
so 0's read comes later.

At time 0 reads: 0 is "written", N-1 is "writing".
N-1 being "writing" means N-1 hasn't completed writing, so N-1 not yet "written".

Following this chain: when i reads, LeftNeighbor(i) is "writing", meaning
LeftNeighbor(i) hasn't reached "written", so LeftNeighbor(i) hasn't read.

So reading order: 1 reads before 0 reads (since when 1 reads, 0 is "writing").
Similarly: 2 reads before 1 reads, etc.
This gives: N-1 reads before N-2 reads before ... before 1 reads before 0 reads.
So N-1 reads first among all.

When N-1 reads, N-2 must be "writing" (for N-1 to read 0).
But also, 0 must be "writing" when N-1 reads (for 0 to later read while N-1 is "writing").
Wait, let's reconsider.

When 0 reads, N-1 is "writing". So N-1 hasn't completed writing.
When 1 reads, 0 is "writing". So 0 hasn't completed writing.
...
When N-1 reads, N-2 is "writing". So N-2 hasn't completed writing.

None have completed writing when they read. But to read, they must be "written".
So when i reads, i is "written" (i completed writing), but LeftNeighbor(i) is "writing"
(LeftNeighbor hasn't completed writing).

So i completed writing before LeftNeighbor(i). For all i. But that's a cycle:
0 completed before N-1 completed before N-2 ... before 1 completed before 0.
Circular ordering is impossible!

Therefore, not all can have read 0. QED.
*)

(* The invariant that captures this: it's impossible for the system to reach a state
   where all are done and all have local = 0. We express this as Safety. *)

(* Theorem: Spec => []Safety *)
THEOREM SafetyTheorem == Spec => []Safety

(* Model checking configuration for N = 8 *)
(* Use TLC to check TypeOK, Safety, and Liveness with N = 8 *)

================================================================================