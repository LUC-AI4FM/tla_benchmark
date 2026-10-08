---- MODULE BufferedRandomAccessFile ----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    FILE_SIZE \* Maximum size of the file
    BUFFER_SIZE \* Size of the buffer

VARIABLES
    position, \* Current position in the file
    buffer,   \* In-memory buffer
    disk,     \* On-disk contents of the file
    valid     \* Validity bitmask for the buffer

Init == /\ position = 0
        /\ buffer = <<ArbitrarySymbol>> ^ BUFFER_SIZE
        /\ disk = <<ArbitrarySymbol>> ^ FILE_SIZE
        /\ valid = {}

Next ==
    \/ Seek
    \/ Read
    \/ Write
    \/ Flush
    \/ SetLength

Seek ==
    \E pos \in 0..FILE_SIZE :
        /\ position' = pos
        /\ UNCHANGED <<buffer, disk, valid>>

Read ==
    \E len \in Nat :
        /\ len > 0
        /\ position + len <= FILE_SIZE
        /\ \A i \in 0..len-1 :
            /\ buffer'[position % BUFFER_SIZE + i] = 
                IF position + i < Len(disk) THEN disk[position + i]
                ELSE ArbitrarySymbol
        /\ valid' = valid \cup {position % BUFFER_SIZE + i : i \in 0..len-1}
        /\ position' = position + len
        /\ UNCHANGED <<disk>>

Write ==
    \E data \in Seq(ArbitrarySymbol) :
        /\ Len(data) > 0
        /\ position + Len(data) <= FILE_SIZE
        /\ \A i \in 0..Len(data)-1 :
            /\ buffer'[position % BUFFER_SIZE + i] = data[i]
            /\ disk'[position + i] = data[i]
        /\ valid' = valid \cup {position % BUFFER_SIZE + i : i \in 0..Len(data)-1}
        /\ position' = position + Len(data)

Flush ==
    /\ \A i \in DOMAIN buffer :
        /\ i \in valid => disk'[i] = buffer[i]
        /\ valid' = {}
        /\ UNCHANGED <<position, buffer>>

SetLength ==
    \E newLen \in 0..FILE_SIZE :
        /\ disk' = Append(disk[1..newLen], <<ArbitrarySymbol>> ^ (FILE_SIZE - newLen))
        /\ position' = MIN(position, newLen)
        /\ valid' = {i \in valid : i < newLen}
        /\ UNCHANGED buffer

Spec ==
    /\ Init
    /\ [][Next]_<<position, buffer, disk, valid>>
    /\ WF_[Next]_<<position, buffer, disk, valid>>

\* Safety invariants
Inv1 == \A i \in DOMAIN buffer : i \notin valid => buffer[i] = ArbitrarySymbol
Inv2 == position \in 0..FILE_SIZE

\* Liveness properties
Liveness == <>[] (/\ valid = {}
                  /\ position = FILE_SIZE)

====