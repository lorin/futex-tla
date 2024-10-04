---- MODULE CAS ----
(***********************)
(* Compare and swap    *)
(***********************)
EXTENDS TLC


(*
  https://lwn.net/Articles/847973/

  From the point of view of a Linux kernel programmer, compare-and-swap has the following prototype:
    T cmpxchg(T *ptr, T old, T new);

  Instead of using *ptr, we use x for the old value and xp (x') for the new one
  This allows us to do:

  cmpxchg(x, x', old, new)

 *)
cmpxchg(x, xp, old, new) == xp = IF x = old THEN new ELSE old




====