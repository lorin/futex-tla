---- MODULE mutex ----
EXTENDS TLC

CONSTANT Processes


(*--algorithm MutualExclusion

variables lock = {};

process p \in Processes
begin
ncs: skip;
acq: await lock = {};
     lock := {self};
cs: skip;
rel: lock := lock \ {self};
     goto ncs;
end process;

end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "a75f7656" /\ chksum(tla) = "7a731c3a")
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ lock = {}
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ lock' = lock

acq(self) == /\ pc[self] = "acq"
             /\ lock = {}
             /\ lock' = {self}
             /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ lock' = lock

rel(self) == /\ pc[self] = "rel"
             /\ lock' = lock \ {self}
             /\ pc' = [pc EXCEPT ![self] = "ncs"]

p(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
