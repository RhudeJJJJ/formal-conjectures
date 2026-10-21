/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0850
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0851
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0852
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0853
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0854
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0855
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0856
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0857
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0858
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0859
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0860
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0861
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0862
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0863
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0864
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0865
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0866
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0867
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0868
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0869
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0870
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0871
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0872
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0873
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0874
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0875
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0876
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0877
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0878
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0879
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0880
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0881
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0882
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0883
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0884
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0885
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0886
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0887
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0888
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0889
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0890
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0891
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0892
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0893
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0894
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0895
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0896
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0897
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0898
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0899
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys17 : ∀ k ∈ keys17, Certified k := by
  apply certified_cons (by exact certified0850)
  apply certified_cons (by exact certified0851)
  apply certified_cons (by exact certified0852)
  apply certified_cons (by exact certified0852swap)
  apply certified_cons (by exact certified0853)
  apply certified_cons (by exact certified0853swap)
  apply certified_cons (by exact certified0854)
  apply certified_cons (by exact certified0855)
  apply certified_cons (by exact certified0856)
  apply certified_cons (by exact certified0856swap)
  apply certified_cons (by exact certified0857)
  apply certified_cons (by exact certified0857swap)
  apply certified_cons (by exact certified0858)
  apply certified_cons (by exact certified0859)
  apply certified_cons (by exact certified0860)
  apply certified_cons (by exact certified0860swap)
  apply certified_cons (by exact certified0861)
  apply certified_cons (by exact certified0861swap)
  apply certified_cons (by exact certified0862)
  apply certified_cons (by exact certified0863)
  apply certified_cons (by exact certified0864)
  apply certified_cons (by exact certified0864swap)
  apply certified_cons (by exact certified0865)
  apply certified_cons (by exact certified0865swap)
  apply certified_cons (by exact certified0866)
  apply certified_cons (by exact certified0867)
  apply certified_cons (by exact certified0868)
  apply certified_cons (by exact certified0868swap)
  apply certified_cons (by exact certified0869)
  apply certified_cons (by exact certified0869swap)
  apply certified_cons (by exact certified0870)
  apply certified_cons (by exact certified0871)
  apply certified_cons (by exact certified0872)
  apply certified_cons (by exact certified0872swap)
  apply certified_cons (by exact certified0873)
  apply certified_cons (by exact certified0873swap)
  apply certified_cons (by exact certified0874)
  apply certified_cons (by exact certified0875)
  apply certified_cons (by exact certified0876)
  apply certified_cons (by exact certified0876swap)
  apply certified_cons (by exact certified0877)
  apply certified_cons (by exact certified0877swap)
  apply certified_cons (by exact certified0878)
  apply certified_cons (by exact certified0879)
  apply certified_cons (by exact certified0880)
  apply certified_cons (by exact certified0880swap)
  apply certified_cons (by exact certified0881)
  apply certified_cons (by exact certified0881swap)
  apply certified_cons (by exact certified0882)
  apply certified_cons (by exact certified0883)
  apply certified_cons (by exact certified0884)
  apply certified_cons (by exact certified0884swap)
  apply certified_cons (by exact certified0885)
  apply certified_cons (by exact certified0885swap)
  apply certified_cons (by exact certified0886)
  apply certified_cons (by exact certified0887)
  apply certified_cons (by exact certified0888)
  apply certified_cons (by exact certified0888swap)
  apply certified_cons (by exact certified0889)
  apply certified_cons (by exact certified0889swap)
  apply certified_cons (by exact certified0890)
  apply certified_cons (by exact certified0891)
  apply certified_cons (by exact certified0892)
  apply certified_cons (by exact certified0892swap)
  apply certified_cons (by exact certified0893)
  apply certified_cons (by exact certified0893swap)
  apply certified_cons (by exact certified0894)
  apply certified_cons (by exact certified0895)
  apply certified_cons (by exact certified0896)
  apply certified_cons (by exact certified0896swap)
  apply certified_cons (by exact certified0897)
  apply certified_cons (by exact certified0897swap)
  apply certified_cons (by exact certified0898)
  apply certified_cons (by exact certified0899)
  simp
#print axioms certified_keys17
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
