# Modeling futexes in TLA+

## References

Ulrich Drepper, [Futexes are tricky][1], June 27, 2004.

Hubertus Franke, Rusty Russel, and Matthew Kirkwood, [Fuss, Futexes and Furwocks: Fast Userlevel Locking in Linux][2], Proceedings of the 2002 Ottawa Linux Summit, 2002.

Darren Hart, [a futex overview and update][3], November 11, 2009


[1]: https://dept-info.labri.fr/~denis/Enseignement/2008-IR/Articles/01-futex.pdf
[2]: https://www.kernel.org/doc/ols/2002/ols2002-pages-479-495.pdf
[3]: https://lwn.net/Articles/360699/

## Code

## Linux kernel

* [Basic futex operation and ordering guarantees (comments)][4]
* [futex_wait]
* [futex_wake]
* [struct futex_hash_bucket]

[4]: https://github.com/torvalds/linux/blob/v6.11/kernel/futex/waitwake.c#L13
[futex_wait]: https://github.com/torvalds/linux/blob/v6.11/kernel/futex/waitwake.c#L688
[futex_wake]: https://github.com/torvalds/linux/blob/v6.11/kernel/futex/waitwake.c#L155
[struct futex_hash_bucket]: https://github.com/torvalds/linux/blob/v6.11/kernel/futex/futex.h#L115

## glibc

[GNU C library POSIX threads implementation (nptl)][nptl].

[nptl]: https://sourceware.org/git/?p=glibc.git;a=tree;f=nptl;hb=HEAD


