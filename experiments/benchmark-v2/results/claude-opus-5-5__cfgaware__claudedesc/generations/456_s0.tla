---- MODULE test64 ----
VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec
====