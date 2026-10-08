MODULE BufferedRandomAccess
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    BufferSize,   (* positive integer *)
    MaxLen,       (* maximum file length *)
    ArbitrarySymbol

VARIABLES FileData, Position, Buffer, AbsFile, AbsPos

(* Record type for buffer *)
BufferRec == [offset : Nat, content : Seq Symbol]

(* Initial state ------------------------------------------------------------*)
Init ==
    /\ FileData \in { s \in Seq Symbol : Len(s) <= MaxLen }
    /\ Position = 0
    /\ AbsFile = FileData
    /\ AbsPos = 0
    /\ Buffer = [offset |-> 0 ;
                 content |-> SubSeq(FileData, 1,
                                   Min(BufferSize, Len(FileData)))]
    
(* Actions ---------------------------------------------------------------*)

SeekAction ==
    \E newPos \in Nat :
        /\ newPos <= Len(FileData)
        /\ Position'   = newPos
        /\ AbsPos'     = newPos
        /\ Buffer'     = [offset |-> newPos ;
                          content |-> SubSeq(FileData, newPos + 1,
