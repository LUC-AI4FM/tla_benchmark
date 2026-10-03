-------------------------- MODULE FischerTimed --------------------------
EXTENDS Integers, TLC

CONSTANTS N,          \* The number of processes
          Delta,      \* The second, longer delay
          Epsilon,    \* The first, shorter delay to set the id
          Infinity    \* A value larger than any timer setting

Procs == 1..N

(* The user prompt mentions a bug for N > 1 and Delta >= Epsilon.
   The standard Fischer algorithm is correct when the time to set the id
   (modeled by Epsilon) is strictly less than the time to wait before
   checking it (modeled by Delta). A mutual exclusion violation
   is expected when Epsilon >= Delta. This specification models that logic. *)
ASSUME N \in 1..3   /\
       Delta \in 1..3  /\
       Epsilon \in 1..3 /\
       Infinity > Delta + Epsilon

(*--algorithm Fischer
variables
  id = 0,
  timers = [i \in Procs |-> Infinity],
  pc = [i \in Procs |-> "Req"] \cup ["ticking" -> "Tick"];

process P(self \in Procs)
begin
Req:
  while TRUE do
    await id = 0;
  SetId_Start:
    timers[self] := Epsilon;
  SetId_End:
    await timers[self] = 0;
    id := self;
    timers[self] := Delta;
  Wait:
    await timers[self] = 0;
    if id = self then
      CS:
        id := 0;
        timers[self] := Infinity;
    else
      timers[self] := Infinity;
      goto Req;
    end if;
  end while
end process;

process ticking
begin
Tick:
  while TRUE do
    either
      with i \in {j \in Procs : timers[j] > 0} do
        timers[i] := timers[i] - 1;
      end with
    or
      skip;
    end either;
  end while
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES id, timers, pc

vars == << id, timers, pc >>

P(self) == \/ pc[self] = "Req" /\ id = 0
               /\ pc' = [pc EXCEPT ![self] = "SetId_Start"]
               /\ UNCHANGED <<id, timers>>
            \/ pc[self] = "SetId_Start"
               /\ timers' = [timers EXCEPT ![self] = Epsilon]
               /\ pc' = [pc EXCEPT ![self] = "SetId_End"]
               /\ UNCHANGED <<id>>
            \/ pc[self] = "SetId_End" /\ timers[self] = 0
               /\ id' = self
               /\ timers' = [timers EXCEPT ![self] = Delta]
               /\ pc' = [pc EXCEPT ![self] = "Wait"]
            \/ pc[self] = "Wait" /\ timers[self] = 0
               /\ \/ /\ id = self
                      /\ pc' = [pc EXCEPT ![self] = "CS"]
                      /\ UNCHANGED <<id, timers>>
                   \/ /\ id /= self
                      /\ timers' = [timers EXCEPT ![self] = Infinity]
                      /\ pc' = [pc EXCEPT ![self] = "Req"]
                      /\ UNCHANGED <<id>>
            \/ pc[self] = "CS"
               /\ id' = 0
               /\ timers' = [timers EXCEPT ![self] = Infinity]
               /\ pc' = [pc EXCEPT ![self] = "Req"]

ticking == pc["ticking"] = "Tick"
             /\ \/ \E i \in {j \in Procs : timers[j] > 0} :
                     timers' = [timers EXCEPT ![i] = timers[i] - 1]
                 \/ UNCHANGED timers
             /\ pc' = [pc EXCEPT !["ticking"] = "Tick"]
             /\ UNCHANGED <<id>>

Init == (* Global variables *)
        /\ id = 0
        /\ timers = [i \in Procs |-> Infinity]
        /\ pc = [i \in Procs |-> "Req"] \cup ["ticking" -> "Tick"]

Next == (\E self \in Procs : P(self))
           \/ ticking
           \/ (* Stuttering *)
              UNCHANGED vars

Fairness == WF_vars(ticking) /\ (\A self \in Procs : WF_vars(P(self)))

Spec == Init /\ [][Next]_vars /\ Fairness
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ id \in 0..N
          /\ timers \in [Procs -> Int]
          /\ pc \in [Procs \cup {"ticking"} -> {"Req", "SetId_Start", "SetId_End", "Wait", "CS", "Tick"}]

MutualExclusion ==
  Cardinality({i \in Procs : pc[i] = "CS"}) <= 1

Liveness ==
  []<> (\E i \in Procs : pc[i] = "CS")

THEOREM Spec => [](TypeOK /\ MutualExclusion) /\ Liveness

=============================================================================