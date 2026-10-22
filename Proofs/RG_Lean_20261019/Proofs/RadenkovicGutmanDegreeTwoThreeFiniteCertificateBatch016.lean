/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0800
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0801
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0802
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0803
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0804
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0805
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0806
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0807
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0808
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0809
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0810
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0811
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0812
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0813
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0814
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0815
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0816
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0817
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0818
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0819
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0820
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0821
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0822
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0823
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0824
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0825
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0826
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0827
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0828
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0829
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0830
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0831
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0832
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0833
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0834
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0835
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0836
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0837
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0838
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0839
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0840
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0841
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0842
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0843
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0844
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0845
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0846
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0847
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0848
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0849
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys016 : ∀ k ∈ keys016, Certified k := by
  apply certified_cons (by exact certified0800)
  apply certified_cons (by exact certified0801)
  apply certified_cons (by exact certified0802)
  apply certified_cons (by exact certified0803)
  apply certified_cons (by exact certified0804)
  apply certified_cons (by exact certified0805)
  apply certified_cons (by exact certified0806)
  apply certified_cons (by exact certified0807)
  apply certified_cons (by exact certified0808)
  apply certified_cons (by exact certified0809)
  apply certified_cons (by exact certified0810)
  apply certified_cons (by exact certified0811)
  apply certified_cons (by exact certified0812)
  apply certified_cons (by exact certified0813)
  apply certified_cons (by exact certified0814)
  apply certified_cons (by exact certified0815)
  apply certified_cons (by exact certified0816)
  apply certified_cons (by exact certified0817)
  apply certified_cons (by exact certified0818)
  apply certified_cons (by exact certified0819)
  apply certified_cons (by exact certified0820)
  apply certified_cons (by exact certified0821)
  apply certified_cons (by exact certified0822)
  apply certified_cons (by exact certified0823)
  apply certified_cons (by exact certified0824)
  apply certified_cons (by exact certified0825)
  apply certified_cons (by exact certified0826)
  apply certified_cons (by exact certified0827)
  apply certified_cons (by exact certified0828)
  apply certified_cons (by exact certified0829)
  apply certified_cons (by exact certified0830)
  apply certified_cons (by exact certified0831)
  apply certified_cons (by exact certified0832)
  apply certified_cons (by exact certified0833)
  apply certified_cons (by exact certified0834)
  apply certified_cons (by exact certified0835)
  apply certified_cons (by exact certified0836)
  apply certified_cons (by exact certified0837)
  apply certified_cons (by exact certified0838)
  apply certified_cons (by exact certified0839)
  apply certified_cons (by exact certified0840)
  apply certified_cons (by exact certified0841)
  apply certified_cons (by exact certified0842)
  apply certified_cons (by exact certified0843)
  apply certified_cons (by exact certified0844)
  apply certified_cons (by exact certified0845)
  apply certified_cons (by exact certified0846)
  apply certified_cons (by exact certified0847)
  apply certified_cons (by exact certified0848)
  apply certified_cons (by exact certified0849)
  simp
#print axioms certified_keys016
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
