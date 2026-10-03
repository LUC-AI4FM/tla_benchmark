------------------------------- MODULE BufferedRandomAccessFile -------------------------------

CONSTANTS Symbols, ArbitrarySymbol, MaxOffset, BuffSz

VARIABLES fileContents, buffer, bufferSize, bufferStart, fileLength

(*--algorithm BufferedRandomAccessFile
variables 
    fileContents = [0..MaxOffset -> ArbitrarySymbol],  \* Initial file contents are arbitrary
    buffer       = [0..BuffSz-1 -> ArbitrarySymbol],   \* Buffer to hold data
    bufferSize   = 0,                                 \* Number of valid bytes in the buffer
    bufferStart  = 0,                                 \* Offset of the first byte in the buffer
    fileLength   = 0;                                  \* Length of the file

fair process (P) = "main"
begin
    while TRUE do
        either
            await /\ TypeOK("seek", <<offset>>)
                 /\ offset \in 0..MaxOffset
            begin
                seek(offset);
                assert SeekCorrect;
                assert SeekEstablishesInv2;
            end
        or
            await /\ TypeOK("read", <<count>>)
                 /\ count \in 1..BuffSz
            begin
                read(count);
                assert Read1Correct;
                assert ReadCorrect;
            end
        or
            await /\ TypeOK("write", <<data>>)
                 /\ data \in Seq(Symbols) 
                 /\ Len(data) \in 1..BuffSz
            begin
                write(data);
                assert Write1Correct;
                assert WriteAtMostCorrect;
            end
        or
            await TypeOK("flush", <<>>)
            begin
                flush();
                assert FlushBufferCorrect;
            end
        or
            await /\ TypeOK("setLength", <<length>>)
                 /\ length \in 0..MaxOffset
            begin
                setLength(length);
            end
        end either;
    od;
end process;

seek(offset) == 
    if offset < bufferStart \/ offset >= bufferStart + bufferSize then
        flush();
        bufferStart := offset;
        bufferSize := 0;
    else
        \* Do nothing, the desired position is already in the buffer
    end if

read(count) ==
    let available = Min(bufferSize - (pc - bufferStart), count) in
        /\ IF available > 0 THEN
            /\ pc := pc + available
            /\ result := SubSeq(buffer, pc - bufferStart, available)
           ELSE
            /\ flush()
            /\ seek(pc)
            /\ read(count)
        ENDIF

write(data) ==
    let dataLen = Len(data) in
        /\ IF bufferSize + dataLen <= BuffSz THEN
            /\ buffer[bufferSize..bufferSize+dataLen-1] := data
            /\ bufferSize := bufferSize + dataLen
           ELSE
            /\ flush()
            /\ seek(bufferStart + bufferSize)
            /\ write(data)
        ENDIF

flush() ==
    /\ fileContents[bufferStart..bufferStart+bufferSize-1] := buffer[0..bufferSize-1]
    /\ bufferSize := 0

setLength(length) ==
    /\ IF length < fileLength THEN
            fileContents[length..fileLength-1] := <<ArbitrarySymbol>>;
       ELSE
            \* Do nothing, extending the file is not handled in this specification
       ENDIF;
    /\ fileLength := length;

TypeOK(op, args) == TRUE  \* Placeholder for type checking

Spec ==
    /\ Init
    /\ [][Next]_<<fileContents, buffer, bufferSize, bufferStart, fileLength>>

Init ==
    /\ fileContents = [0..MaxOffset -> ArbitrarySymbol]
    /\ buffer       = [0..BuffSz-1 -> ArbitrarySymbol]
    /\ bufferSize   = 0
    /\ bufferStart  = 0
    /\ fileLength   = 0

Next ==
    \/ \E offset \in 0..MaxOffset : seek(offset) /\ SeekCorrect /\ SeekEstablishesInv2
    \/ \E count \in 1..BuffSz : read(count) /\ Read1Correct /\ ReadCorrect
    \/ \E data \in Seq(Symbols) \land Len(data) \in 1..BuffSz : write(data) /\ Write1Correct /\ WriteAtMostCorrect
    \/ flush() /\ FlushBufferCorrect
    \/ \E length \in 0..MaxOffset : setLength(length)

Inv1 == 
    /\ bufferSize \in 0..BuffSz
    /\ bufferStart \in 0..MaxOffset

Inv2CanAlwaysBeRestored ==
    /\ TRUE  \* Placeholder for the condition that Inv2 can always be restored

Inv3 ==
    /\ \A i \in 0..bufferSize-1 : fileContents[bufferStart+i] = buffer[i]

Inv4 ==
    /\ fileLength \in 0..MaxOffset

Inv5 ==
    /\ \A i \in fileLength..MaxOffset : fileContents[i] = ArbitrarySymbol

Safety == 
    /\ Inv1
    /\ Inv3
    /\ Inv4
    /\ Inv5

FlushBufferCorrect ==
    /\ \A i \in 0..bufferSize-1 : fileContents[bufferStart+i] = buffer[i]
    /\ bufferSize' = 0

SeekCorrect ==
    /\ bufferStart' = pc
    /\ bufferSize' = 0

SeekEstablishesInv2 ==
    /\ TRUE  \* Placeholder for the condition that Seek establishes Inv2

Write1Correct ==
    /\ \A i \in 0..Len(data)-1 : buffer[bufferSize+i] = data[i]
    /\ bufferSize' = bufferSize + Len(data)

Read1Correct ==
    /\ result = SubSeq(buffer, pc - bufferStart, available)
    /\ pc' = pc + available

WriteAtMostCorrect ==
    /\ \A i \in 0..Len(data)-1 : fileContents[bufferStart+bufferSize+i] = data[i]
    /\ bufferSize' = bufferSize + Len(data)

ReadCorrect ==
    /\ result = SubSeq(fileContents, pc, count)
    /\ pc' = pc + count

=============================================================================