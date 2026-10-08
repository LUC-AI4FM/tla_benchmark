--------------------------- MODULE BoundedQueue ---------------------------
EXTENDS Integers, Sequences

CONSTANT N, Clients, Values
VARIABLE queue, results

Init == (queue = <<>>) ∧ (results = [c ∈ Clients |-> "neutral"])

Enqueue(c, v) == 
  ∨ (¬IsFull(queue)) ∧ (queue' = Append(queue, v)) ∧ (results' = [results EXCEPT ![c] = "success"])
  ∨ (¬IsFull(queue)) ∧ (queue' = Prepend(v, queue)) ∧ (results' = [results EXCEPT ![c] = "success"])
  ∨ (IsFull(queue)) ∧ (UNCHANGED queue) ∧ (results' = [results EXCEPT ![c] = "full"])

Dequeue(c) == 
  ∨ (∃ v ∈ queue : (queue' = Tail(queue)) ∧ (results' = [results EXCEPT ![c] = Head(queue)]))
  ∨ (∃ v ∈ queue : (queue' = SubSeq(queue, 2, Len(queue))) ∧ (results' = [results EXCEPT ![c] = queue[Len(queue)]]))
  ∨ (queue = <<>>) ∧ (UNCHANGED queue) ∧ (results' = [results EXCEPT ![c] = "empty"])

Reset(c) == (results' = [results EXCEPT ![c] = "neutral"]) ∧ (UNCHANGED queue)

Next(c) == 
  (∃ v ∈ Values : Enqueue(c, v)) ∨ Dequeue(c) ∨ Reset(c)

Spec == Init ∧ [][∀ c ∈ Clients : Next(c)]_queue ∧ [][∀ c ∈ Clients : Next(c)]_results

THEOREM Spec => []Length(queue) ≤ N
THEOREM Spec => []∀ c ∈ Clients : results[c] ≠ "success" ∨ results[c] ∈ queue
THEOREM Spec => []∀ c ∈ Clients, v ∈ Values : 
  (Enqueue(c, v)) ∧ (results' = [results EXCEPT ![c] = "success"]) => (v ∈ queue')

THEOREM Spec => WF_(∃ v ∈ Values : Enqueue(_, v))_queue
THEOREM Spec => WF_(Dequeue(_))_queue

Val == Values
=============================================================================