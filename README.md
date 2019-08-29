# basic-paxos
This directory contains proofs for Basic Paxos for single valued consensus.

1. PaxosLam.tla:
TLA+ specification of Basic Paxos as in
<https://github.com/tlaplus/v1-tlapm/blob/master/examples/paxos/Paxos.tla>.
Following modifications have been made to the file:

    1. Moved lemmas `QuorumNonEmpty` and `NoneNotAValue` after definition of `Spec`. This is done to get true specification line count easily.
      
    2. Commented the following:
        1. `chosenBar`, line 541
        2. `C`, line 543
        3. Theorem `Refinement`, line 549---567
      
       This is done because our goal is to prove Safety of the specification, not to prove that it also refines some other specification.
   
2. PaxosHistVarNFM.tla:
TLA+ specification and proof of Basic Paxos using History variables as described in \[3\].

# multi-paxos
This directory contains proofs for Multi-Paxos for multi valued consensus.

1. MultiPaxosFM16.tla:
TLA+ specification and proof of Multi-Paxos as described in \[1\].

2. MultiPaxos.tla:
An improved TLA+ specification and proof of Multi-Paxos compared to MultiPaxosFM16.tla. These improvements are described in \[2\].

3. MultiPaxosHistVarNFM.tla:
TLA+ specification and proof of Multi-Paxos using History variables as described in \[3\].

# multi-paxos-preemption
This directory contains proofs for Multi-Paxos with Preemption. Preemption specifies when and how proposers abandon their current proposal number and pick a new one.

1. MultiPaxosPreemptionFM16.tla:
TLA+ specification and proof of Multi-Paxos with Preemption
as described in \[1\].

2. MultiPaxosPreemption.tla:
An improved TLA+ specification and proof of Multi-Paxos with Preemption compared to MultiPaxosPreemptionFM16.tla. These improvements are described in \[2\].

3. MultiPaxosPreemptionHistVarNFM.tla:
TLA+ specification and proof of Multi-Paxos with Preemption using History variables as described in \[3\].

# References
\[1\] Chand, S., Liu, Y. A., & Stoller, S. D. (2016, November). Formal Verification of Multi-Paxos for Distributed Consensus. In International Symposium on Formal Methods (pp. 119-136). [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-319-48989-6_8)

\[2\] Chand, S., Liu, Y. A., & Stoller, S. D. (2019, January). Formal Verification of Multi-Paxos for Distributed Consensus. arXiv preprint arXiv:1606.01387. [arXiv](https://arxiv.org/abs/1606.01387)

\[3\] Chand, S., & Liu, Y. A. (2018, April). Simpler specifications and easier proofs of distributed algorithms using history variables. In NASA Formal Methods Symposium (pp. 70-86). [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-319-77935-5_5)
