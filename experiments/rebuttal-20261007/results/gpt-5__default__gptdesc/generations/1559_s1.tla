---- MODULE LockWithAux ----
EXTENDS Naturals, Sequences

(*
  Lock protocol with auxiliary variables to relate to Peterson.
  - h_turn: history of assigned values to 'turn'
  - s: stuttering stage to mimic Peterson's three-step entry protocol
*)

CONSTANTS

Proc == {0, 1}

Other(i) == 1 - i

VARIABLES
  owner,     \* "none" or the process id that currently owns the lock
  mode,      \* per-process abstract mode: "idle", "trying", "cs"
  flag,      \* per-process intention flag (as in Peterson)
  turn,      \* the turn variable (as in Peterson)
  s,         \* per-process stuttering stage: 0 (none), 1 (set flag), 2 (set turn), 3 (await)
  h_turn     \* sequence recording the history of assignments to 'turn'

vars == << owner, mode, flag, turn, s, h_turn >>

TypeInv ==
  /\ owner \in Proc \cup {"none"}
  /\ mode \in [Proc -> {"idle", "trying", "cs"}]
  /\ flag \in [Proc -> BOOLEAN]
  /\ turn \in Proc
  /\ s \in [Proc -> 0..3]
  /\ h_turn \in Seq(Proc)

Mutex ==
  ~(mode[0] = "cs" /\ mode[1] = "cs")

OwnerConsistent ==
  /\ \A i \in Proc : (mode[i] = "cs") => owner = i

Inv == TypeInv /\ Mutex /\ OwnerConsistent

Init ==
  /\ owner = "none"
  /\ mode = [i \in Proc |-> "idle"]
  /\ flag = [i \in Proc |-> FALSE]
  /\ s = [i \in Proc |-> 0]
  /\ turn \in Proc
  /\ h_turn = << >>

StartTry(i) ==
  /\ i \in Proc
  /\ mode[i] = "idle"
  /\ mode' = [mode EXCEPT ![i] = "trying"]
  /\ UNCHANGED << owner, flag, turn, s, h_turn >>

BeginEntry(i) ==
  /\ i \in Proc
  /\ mode[i] = "trying"
  /\ s[i] = 0
  /\ s' = [s EXCEPT ![i] = 1]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ UNCHANGED << owner, turn, h_turn, mode >>

AssignTurn(i) ==
  /\ i \in Proc
  /\ s[i] = 1
  /\ s' = [s EXCEPT ![i] = 2]
  /\ turn' = Other(i)
  /\ h_turn' = Append(h_turn, Other(i))
  /\ UNCHANGED << owner, flag, mode >>

AwaitStage(i) ==
  /\ i \in Proc
  /\ s[i] = 2
  /\ s' = [s EXCEPT ![i] = 3]
  /\ UNCHANGED << owner, flag, turn, h_turn, mode >>

EnterCS(i) ==
  /\ i \in Proc
  /\ s[i] = 3
  /\ owner = "none"
  /\ (flag[Other(i)] = FALSE \/ turn = i)
  /\ owner' = i
  /\ mode' = [mode EXCEPT ![i] = "cs"]
  /\ s' = [s EXCEPT ![i] = 0]
  /\ UNCHANGED << flag, turn, h_turn >>

Release(i) ==
  /\ i \in Proc
  /\ mode[i] = "cs"
  /\ owner = i
  /\ owner' = "none"
  /\ mode' = [mode EXCEPT ![i] = "idle"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ UNCHANGED << turn, s, h_turn >>

Next ==
  \E i \in Proc :
       StartTry(i)
    \/ BeginEntry(i)
    \/ AssignTurn(i)
    \/ AwaitStage(i)
    \/ EnterCS(i)
    \/ Release(i)

Fairness ==
  /\ \A i \in Proc : WF_vars(BeginEntry(i))
  /\ \A i \in Proc : WF_vars(AssignTurn(i))
  /\ \A i \in Proc : WF_vars(AwaitStage(i))
  /\ \A i \in Proc : WF_vars(EnterCS(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(*
  Map Lock-with-aux states to Peterson control states via the stuttering stage s:
    - s = 0 and not in cs => "idle"
    - s = 1 => "setflag"
    - s = 2 => "setturn"
    - s = 3 => "wait"
    - mode = "cs" => "cs"
*)
PcPet ==
  [ i \in Proc |->
      IF mode[i] = "cs" THEN "cs"
      ELSE IF s[i] = 0 THEN "idle"
      ELSE IF s[i] = 1 THEN "setflag"
      ELSE IF s[i] = 2 THEN "setturn"
      ELSE "wait"
  ]

INSTANCE Peterson
  WITH Proc <- Proc,
       flag <- flag,
       turn <- turn,
       pc   <- PcPet

====