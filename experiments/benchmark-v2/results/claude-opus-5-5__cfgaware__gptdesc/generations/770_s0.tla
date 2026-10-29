---------------------------- MODULE ringbuffer ----------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots, indexed modulo  *)
(* the buffer size.  Each slot holds either an element of Values or NULL.  *)
(*                                                                         *)
(* To model reads and writes that take more than one step, the module also *)
(* tracks which readers and writers are currently accessing each slot.     *)
(*                                                                         *)
(* NOTE: Client specifications that use this module should include         *)
(* NoDataRaces as an invariant.                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Size,      \* number of slots in the ring buffer
          Values,    \* the set of values that may be stored
          NULL       \* distinguished "empty" value

ASSUME SizeAssumption == Size \in Nat \ {0}
ASSUME NullAssumption == NULL \notin Values

VARIABLE ringbuffer

LastIndex == Size - 1

Indices == 0..LastIndex

\* Map an arbitrary natural-number position onto a slot index
IndexOf(i) == i % Size

(***************************************************************************)
(* Initial state: every slot empty, no readers, no writers.                *)
(***************************************************************************)
Init ==
    ringbuffer = [slots   |-> [j \in Indices |-> NULL],
                  readers |-> [j \in Indices |-> {}],
                  writers |-> [j \in Indices |-> {}]]

(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOk ==
    /\ ringbuffer.slots \in [Indices -> Values \cup {NULL}]
    /\ DOMAIN ringbuffer.readers = Indices
    /\ DOMAIN ringbuffer.writers = Indices
    /\ \A j \in Indices : IsFiniteSet(ringbuffer.readers[j])
    /\ \A j \in Indices : IsFiniteSet(ringbuffer.writers[j])

(***************************************************************************)
(* Reading: a reader first registers itself on the slot (BeginRead), may   *)
(* observe the value (Read), and then deregisters (EndRead).               *)
(***************************************************************************)
BeginRead(i, actor) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[IndexOf(i)] = @ \cup {actor}]

Read(i) == ringbuffer.slots[IndexOf(i)]

EndRead(i, actor) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[IndexOf(i)] = @ \ {actor}]

(***************************************************************************)
(* Writing: a writer stores a value into the slot and registers itself as  *)
(* writing (Write), then later deregisters (EndWrite).                     *)
(***************************************************************************)
Write(i, actor, val) ==
    ringbuffer' = [ringbuffer EXCEPT !.slots[IndexOf(i)]   = val,
                                     !.writers[IndexOf(i)] = @ \cup {actor}]

EndWrite(i, actor) ==
    ringbuffer' = [ringbuffer EXCEPT !.writers[IndexOf(i)] = @ \ {actor}]

(***************************************************************************)
(* No data races: while a slot is being written, there is exactly one      *)
(* writer and no readers accessing it.                                     *)
(*                                                                         *)
(* Client specifications should include NoDataRaces as an invariant.      *)
(***************************************************************************)
NoDataRaces ==
    \A j \in Indices :
        ringbuffer.writers[j] # {} =>
            /\ ringbuffer.readers[j] = {}
            /\ Cardinality(ringbuffer.writers[j]) = 1

=============================================================================