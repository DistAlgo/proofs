## PaxosLam.tla
This is the TLA+ specification of Basic Paxos (single-valued) Paxos as in
<https://github.com/tlaplus/v1-tlapm/blob/master/examples/paxos/Paxos.tla>.
Following modifications have been made to the file:

1. Moving lemmas `QuorumNonEmpty` and `NoneNotAValue` after definition of
   `Spec`. This is done to get true specification line count easily.
      
2. Commenting the following:
     1. `chosenBar`, line 541
     2. `C`, line 543
     3. Theorem `Refinement`, line 549---567
      
   This is done because our goal is to prove Safety of the specification,
   not to prove that it also refines some other specification.
