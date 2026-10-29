--------------------------- MODULE test64 ---------------------------
\* Changed module name from Test64 because that's now illegal

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec

=============================================================================