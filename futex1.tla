---- MODULE futex1 ----
EXTENDS TLC

CONSTANTS Processes, Addresses, Free, Acquired, Contended
Values == {Free, Acquired, Contended}

(*--algorithm futex 

variables 
    mem = [x \in Addresses |-> Free],
    a \in Addresses;

macro cmpxchg(x, xwas, old, new) begin
    xwas := x;
    if x = old then 
        x := new;
    end if;
end macro;


procedure lock() begin
L1: 
    if mem[a] = Free then
        mem[a] := Acquired;
    end if
end procedure;


procedure unlock() begin
U1: skip;
end procedure;

process p \in Processes
begin
    ncs: skip;
    acq: call lock();
    cs: skip;
    rel: call unlock();
         goto ncs;
end process;

end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "bbf5cfbe" /\ chksum(tla) = "1fd41627")
VARIABLES pc, mem, a, stack

vars == << pc, mem, a, stack >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mem = [x \in Addresses |-> Free]
        /\ a \in Addresses
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ncs"]

L1(self) == /\ pc[self] = "L1"
            /\ IF mem[a] = Free
                  THEN /\ mem' = [mem EXCEPT ![a] = Acquired]
                  ELSE /\ TRUE
                       /\ mem' = mem
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << a, stack >>

lock(self) == L1(self)

U1(self) == /\ pc[self] = "U1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Error"]
            /\ UNCHANGED << mem, a, stack >>

unlock(self) == U1(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED << mem, a, stack >>

acq(self) == /\ pc[self] = "acq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                      pc        |->  "cs" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << mem, a >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED << mem, a, stack >>

rel(self) == /\ pc[self] = "rel"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                      pc        |->  "ncs" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "U1"]
             /\ UNCHANGED << mem, a >>

p(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: lock(self) \/ unlock(self))
           \/ (\E self \in Processes: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
