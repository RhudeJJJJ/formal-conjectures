/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0850
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0851
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0852
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0853
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0854
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0855
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0856
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0857
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0858
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0859
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0860
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0861
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0862
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0863
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0864
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0865
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0866
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0867
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0868
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0869
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0870
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0871
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0872
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0873
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0874
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0875
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0876
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0877
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0878
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0879
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0880
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0881
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0882
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0883
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0884
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0885
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0886
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0887
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0888
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0889
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0890
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0891
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0892
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0893
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0894
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0895
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0896
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0897
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0898
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0899
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys017 : ∀ k ∈ keys017, Certified k := by
  apply certified_cons (by exact certified0850)
  apply certified_cons (by exact certified0851)
  apply certified_cons (by exact certified0852)
  apply certified_cons (by exact certified0853)
  apply certified_cons (by exact certified0854)
  apply certified_cons (by exact certified0855)
  apply certified_cons (by exact certified0856)
  apply certified_cons (by exact certified0857)
  apply certified_cons (by exact certified0858)
  apply certified_cons (by exact certified0859)
  apply certified_cons (by exact certified0860)
  apply certified_cons (by exact certified0861)
  apply certified_cons (by exact certified0862)
  apply certified_cons (by exact certified0863)
  apply certified_cons (by exact certified0864)
  apply certified_cons (by exact certified0865)
  apply certified_cons (by exact certified0866)
  apply certified_cons (by exact certified0867)
  apply certified_cons (by exact certified0868)
  apply certified_cons (by exact certified0869)
  apply certified_cons (by exact certified0870)
  apply certified_cons (by exact certified0871)
  apply certified_cons (by exact certified0872)
  apply certified_cons (by exact certified0873)
  apply certified_cons (by exact certified0874)
  apply certified_cons (by exact certified0875)
  apply certified_cons (by exact certified0876)
  apply certified_cons (by exact certified0877)
  apply certified_cons (by exact certified0878)
  apply certified_cons (by exact certified0879)
  apply certified_cons (by exact certified0880)
  apply certified_cons (by exact certified0881)
  apply certified_cons (by exact certified0882)
  apply certified_cons (by exact certified0883)
  apply certified_cons (by exact certified0884)
  apply certified_cons (by exact certified0885)
  apply certified_cons (by exact certified0886)
  apply certified_cons (by exact certified0887)
  apply certified_cons (by exact certified0888)
  apply certified_cons (by exact certified0889)
  apply certified_cons (by exact certified0890)
  apply certified_cons (by exact certified0891)
  apply certified_cons (by exact certified0892)
  apply certified_cons (by exact certified0893)
  apply certified_cons (by exact certified0894)
  apply certified_cons (by exact certified0895)
  apply certified_cons (by exact certified0896)
  apply certified_cons (by exact certified0897)
  apply certified_cons (by exact certified0898)
  apply certified_cons (by exact certified0899)
  simp
#print axioms certified_keys017
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
