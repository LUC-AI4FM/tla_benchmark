------------------------------- MODULE TwoStateController ------------------------------

CONSTANTS MaxHistoryLength

VARIABLES mode, history

(* --algorithm TwoStateController
variables 
    mode \in {"Mode1", "Mode2"},
    history \in SUBSET {"Mode1", "Mode2"}:> Nat;

begin
    Init:
        /\ mode = "Mode1"
        /\ history = << >>;

    Next ==
        \/ /\ mode = "Mode1"
           /\ \/ \/ history' = Append(history, "Mode1")
                  /\ mode' = "Mode2"
              \/ /\ history' = history
                 /\ mode' = "Mode1"
        \/ /\ mode = "Mode2"
           /\ \/ \/ history' = Append(history, "Mode2")
                  /\ mode' = "Mode1"
              \/ /\ history' = history
                 /\ mode' = "Mode2";

    Spec ==
        Init /\ [][Next]_<<mode, history>>;

    Termination ==
        /\ mode = "Done"
        /\ history \in SUBSET {"Mode1", "Mode2"}:> Nat;

    HistoryLengthBound ==
        Len(history) < MaxHistoryLength;

    Fairness ==
        WF_next(<>UNCHANGED <<mode, history>>)

    Liveness ==
        <>[](Termination);

end algorithm *)

Spec == Init /\ [][Next]_<<mode, history>> /\ SF_Fairness

Init ==
    /\ mode = "Mode1"
    /\ history = << >>

Next ==
    \/ /\ mode = "Mode1"
       /\ \/ \/ history' = Append(history, "Mode1")
              /\ mode' = "Mode2"
          \/ /\ history' = history
             /\ mode' = "Mode1"
    \/ /\ mode = "Mode2"
       /\ \/ \/ history' = Append(history, "Mode2")
              /\ mode' = "Mode1"
          \/ /\ history' = history
             /\ mode' = "Mode2"

Termination ==
    /\ mode = "Done"
    /\ history \in SUBSET {"Mode1", "Mode2"}:> Nat

HistoryLengthBound ==
    Len(history) < MaxHistoryLength

Fairness ==
    WF_next(<>UNCHANGED <<mode, history>>)

Liveness ==
    <>[](Termination)

SF_Fairness ==
    SF_next(<>UNCHANGED <<mode, history>>)

=============================================================================