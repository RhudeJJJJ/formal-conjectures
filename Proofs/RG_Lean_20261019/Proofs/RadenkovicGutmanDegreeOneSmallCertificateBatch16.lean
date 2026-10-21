/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0800
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0801
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0802
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0803
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0804
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0805
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0806
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0807
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0808
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0809
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0810
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0811
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0812
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0813
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0814
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0815
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0816
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0817
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0818
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0819
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0820
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0821
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0822
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0823
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0824
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0825
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0826
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0827
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0828
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0829
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0830
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0831
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0832
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0833
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0834
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0835
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0836
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0837
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0838
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0839
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0840
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0841
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0842
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0843
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0844
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0845
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0846
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0847
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0848
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0849
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys16 : ∀ k ∈ keys16, Certified k := by
  apply certified_cons (by exact certified0800)
  apply certified_cons (by exact certified0800swap)
  apply certified_cons (by exact certified0801)
  apply certified_cons (by exact certified0801swap)
  apply certified_cons (by exact certified0802)
  apply certified_cons (by exact certified0803)
  apply certified_cons (by exact certified0804)
  apply certified_cons (by exact certified0804swap)
  apply certified_cons (by exact certified0805)
  apply certified_cons (by exact certified0805swap)
  apply certified_cons (by exact certified0806)
  apply certified_cons (by exact certified0807)
  apply certified_cons (by exact certified0808)
  apply certified_cons (by exact certified0808swap)
  apply certified_cons (by exact certified0809)
  apply certified_cons (by exact certified0809swap)
  apply certified_cons (by exact certified0810)
  apply certified_cons (by exact certified0811)
  apply certified_cons (by exact certified0812)
  apply certified_cons (by exact certified0812swap)
  apply certified_cons (by exact certified0813)
  apply certified_cons (by exact certified0813swap)
  apply certified_cons (by exact certified0814)
  apply certified_cons (by exact certified0815)
  apply certified_cons (by exact certified0816)
  apply certified_cons (by exact certified0816swap)
  apply certified_cons (by exact certified0817)
  apply certified_cons (by exact certified0817swap)
  apply certified_cons (by exact certified0818)
  apply certified_cons (by exact certified0819)
  apply certified_cons (by exact certified0820)
  apply certified_cons (by exact certified0820swap)
  apply certified_cons (by exact certified0821)
  apply certified_cons (by exact certified0821swap)
  apply certified_cons (by exact certified0822)
  apply certified_cons (by exact certified0823)
  apply certified_cons (by exact certified0824)
  apply certified_cons (by exact certified0824swap)
  apply certified_cons (by exact certified0825)
  apply certified_cons (by exact certified0825swap)
  apply certified_cons (by exact certified0826)
  apply certified_cons (by exact certified0827)
  apply certified_cons (by exact certified0828)
  apply certified_cons (by exact certified0828swap)
  apply certified_cons (by exact certified0829)
  apply certified_cons (by exact certified0829swap)
  apply certified_cons (by exact certified0830)
  apply certified_cons (by exact certified0831)
  apply certified_cons (by exact certified0832)
  apply certified_cons (by exact certified0832swap)
  apply certified_cons (by exact certified0833)
  apply certified_cons (by exact certified0833swap)
  apply certified_cons (by exact certified0834)
  apply certified_cons (by exact certified0835)
  apply certified_cons (by exact certified0836)
  apply certified_cons (by exact certified0836swap)
  apply certified_cons (by exact certified0837)
  apply certified_cons (by exact certified0837swap)
  apply certified_cons (by exact certified0838)
  apply certified_cons (by exact certified0839)
  apply certified_cons (by exact certified0840)
  apply certified_cons (by exact certified0840swap)
  apply certified_cons (by exact certified0841)
  apply certified_cons (by exact certified0841swap)
  apply certified_cons (by exact certified0842)
  apply certified_cons (by exact certified0843)
  apply certified_cons (by exact certified0844)
  apply certified_cons (by exact certified0844swap)
  apply certified_cons (by exact certified0845)
  apply certified_cons (by exact certified0845swap)
  apply certified_cons (by exact certified0846)
  apply certified_cons (by exact certified0847)
  apply certified_cons (by exact certified0848)
  apply certified_cons (by exact certified0848swap)
  apply certified_cons (by exact certified0849)
  apply certified_cons (by exact certified0849swap)
  simp
#print axioms certified_keys16
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
