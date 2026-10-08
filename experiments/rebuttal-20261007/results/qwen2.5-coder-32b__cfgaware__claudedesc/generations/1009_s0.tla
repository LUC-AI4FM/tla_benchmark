------------------------------- MODULE BufferedRandomAccessFile -------------------------------

CONSTANTS BuffSz, MaxOffset

VARIABLES dirty, length, curr, lo, buff, diskPos, file_content, file_pointer

(*--algorithm BufferedRandomAccessFile

variables 
    dirty \in BOOLEAN,
    length \in 0..MaxOffset,
    curr \in 0..MaxOffset,
    lo \in 0..MaxOffset,
    buff \in [0..BuffSz-1 -> 0..255],
    diskPos \in 0..MaxOffset,
    file_content \in [0..MaxOffset -> 0..255],
    file_pointer \in 0..MaxOffset

define
    LogicalFileContent ==
        [i \in 0..length-1 |-> IF i \in lo..lo+BuffSz-1 THEN buff[i-lo] ELSE file_content[i]]

    Inv1 == /\ length \leq MaxOffset
            /\ curr \leq length
            /\ lo \leq diskPos
            /\ diskPos \leq lo + BuffSz

    Inv2 == \/ ~dirty
            \/ (lo <= curr /\ curr < lo + BuffSz)

    Inv3 == \A i \in 0..length-1 : LogicalFileContent[i] = file_content[i]

    Inv4 == \A i \in 0..BuffSz-1 : buff[i] \in 0..255

    Inv5 == diskPos \leq MaxOffset

    TypeOK ==
        /\ dirty \in BOOLEAN
        /\ length \in 0..MaxOffset
        /\ curr \in 0..length
        /\ lo \in 0..diskPos
        /\ diskPos \in lo..lo+BuffSz
        /\ buff \in [0..BuffSz-1 -> 0..255]
        /\ file_content \in [0..MaxOffset -> 0..255]
        /\ file_pointer \in 0..length

    FlushBuffer ==
        IF dirty THEN
            /\ diskPos' = lo
            /\ \A i \in 0..BuffSz-1 : 
                (lo + i < length => file_content'[(lo + i)] = buff[i])
            /\ dirty'
        ELSE
            UNCHANGED <<diskPos, file_content, dirty>>

    Seek ==
        /\ diskPos' = curr
        /\ IF ~Inv2 THEN
                /\ lo' = curr - (curr MOD BuffSz)
                /\ \A i \in 0..BuffSz-1 : 
                    (lo' + i < length => buff'[i] = file_content[lo' + i])
                /\ dirty'
           ELSE
               UNCHANGED <<lo, buff, dirty>>
        /\ curr' = curr

    SetLength ==
        /\ IF length > curr THEN
                /\ \A i \in curr..length-1 : file_content'[i] = 0
           ELSE
               UNCHANGED file_content
        /\ length' = curr

    Read1 ==
        /\ curr < length
        /\ LET byte == LogicalFileContent[curr]
           IN /\ diskPos' = IF ~Inv2 THEN curr ELSE diskPos
              /\ buff' = IF ~Inv2 THEN [i \in 0..BuffSz-1 |-> file_content[lo + i]] ELSE buff
              /\ dirty' = IF ~Inv2 THEN FALSE ELSE dirty
              /\ lo' = IF ~Inv2 THEN curr - (curr MOD BuffSz) ELSE lo
              /\ curr' = curr + 1
              /\ file_pointer' = curr
              /\ file_content' = file_content

    Write1 ==
        /\ curr < length
        /\ LET byte \in 0..255
           IN /\ diskPos' = IF ~Inv2 THEN curr ELSE diskPos
              /\ buff'[curr - lo] = byte
              /\ dirty' = TRUE
              /\ lo' = IF ~Inv2 THEN curr - (curr MOD BuffSz) ELSE lo
              /\ curr' = curr + 1
              /\ file_pointer' = curr

    ReadAtMost ==
        /\ curr < length
        /\ LET n \in 0..(length - curr)
           IN /\ diskPos' = IF ~Inv2 THEN curr ELSE diskPos
              /\ buff' = IF ~Inv2 THEN [i \in 0..BuffSz-1 |-> file_content[lo + i]] ELSE buff
              /\ dirty' = IF ~Inv2 THEN FALSE ELSE dirty
              /\ lo' = IF ~Inv2 THEN curr - (curr MOD BuffSz) ELSE lo
              /\ curr' = curr + n
              /\ file_pointer' = curr
              /\ file_content' = file_content

    WriteAtMost ==
        /\ curr < length
        /\ LET bytes \in [0..(length - curr) -> 0..255]
           IN /\ diskPos' = IF ~Inv2 THEN curr ELSE diskPos
              /\ buff' = [i \in 0..BuffSz-1 |-> 
                              IF lo + i < length /\ i < LEN(bytes)
                              THEN bytes[i] 
                              ELSE (IF lo + i < length THEN buff[i] ELSE file_content[lo + i])]
              /\ dirty' = TRUE
              /\ lo' = IF ~Inv2 THEN curr - (curr MOD BuffSz) ELSE lo
              /\ curr' = curr + LEN(bytes)
              /\ file_pointer' = curr

    Init ==
        /\ dirty = FALSE
        /\ length = 0
        /\ curr = 0
        /\ lo = 0
        /\ buff = [i \in 0..BuffSz-1 |-> 0]
        /\ diskPos = 0
        /\ file_content = [i \in 0..MaxOffset |-> 0]
        /\ file_pointer = 0

    Next ==
        \/ FlushBuffer
        \/ Seek
        \/ SetLength
        \/ Read1
        \/ Write1
        \/ ReadAtMost
        \/ WriteAtMost

    Spec ==
        Init /\ [][Next]_<<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>

    Symbols == {MaxOffset, BuffSz}

    ArbitrarySymbol == CHOOSE x \in Symbols : TRUE

    Inv2CanAlwaysBeRestored ==
        [](Inv2 \/ <>[<FlushBuffer; Seek>]_<<dirty, length, curr, lo, buff, diskPos, file_content, file_pointer>>)

    FlushBufferCorrect ==
        [](FlushBuffer => UNCHANGED <<file_pointer, curr>> /\ ~dirty')

    SeekCorrect ==
        [](Seek => UNCHANGED <<file_content, length>>)

    SeekEstablishesInv2 ==
        [](Seek => Inv2')

    Write1Correct ==
        [](Write1 => UNCHANGED <<length, file_pointer>>)

    Read1Correct ==
        [](Read1 => UNCHANGED <<dirty, buff, lo, diskPos>>)

    WriteAtMostCorrect ==
        [](WriteAtMost => UNCHANGED <<file_pointer, length>>)

    ReadCorrect ==
        [](ReadAtMost => UNCHANGED <<dirty, buff, lo, diskPos>>)

    Safety ==
        Spec /\ []TypeOK /\ []Inv1 /\ []Inv2 /\ []Inv3 /\ []Inv4 /\ []Inv5

end algorithm *)
=============================================================================