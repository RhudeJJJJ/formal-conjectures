/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0900
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0901
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0902
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0903
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0904
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0905
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0906
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0907
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0908
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0909
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0910
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0911
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0912
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0913
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0914
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0915
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0916
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0917
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0918
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0919
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0920
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0921
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0922
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0923
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0924
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0925
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0926
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0927
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0928
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0929
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0930
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0931
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0932
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0933
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0934
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0935
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0936
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0937
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0938
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0939
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0940
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0941
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0942
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0943
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0944
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0945
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0946
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0947
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0948
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0949
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys18 : ∀ k ∈ keys18, Certified k := by
  apply certified_cons (by exact certified0900)
  apply certified_cons (by exact certified0900swap)
  apply certified_cons (by exact certified0901)
  apply certified_cons (by exact certified0901swap)
  apply certified_cons (by exact certified0902)
  apply certified_cons (by exact certified0903)
  apply certified_cons (by exact certified0904)
  apply certified_cons (by exact certified0904swap)
  apply certified_cons (by exact certified0905)
  apply certified_cons (by exact certified0905swap)
  apply certified_cons (by exact certified0906)
  apply certified_cons (by exact certified0907)
  apply certified_cons (by exact certified0908)
  apply certified_cons (by exact certified0908swap)
  apply certified_cons (by exact certified0909)
  apply certified_cons (by exact certified0909swap)
  apply certified_cons (by exact certified0910)
  apply certified_cons (by exact certified0911)
  apply certified_cons (by exact certified0912)
  apply certified_cons (by exact certified0912swap)
  apply certified_cons (by exact certified0913)
  apply certified_cons (by exact certified0913swap)
  apply certified_cons (by exact certified0914)
  apply certified_cons (by exact certified0915)
  apply certified_cons (by exact certified0916)
  apply certified_cons (by exact certified0916swap)
  apply certified_cons (by exact certified0917)
  apply certified_cons (by exact certified0917swap)
  apply certified_cons (by exact certified0918)
  apply certified_cons (by exact certified0919)
  apply certified_cons (by exact certified0920)
  apply certified_cons (by exact certified0920swap)
  apply certified_cons (by exact certified0921)
  apply certified_cons (by exact certified0921swap)
  apply certified_cons (by exact certified0922)
  apply certified_cons (by exact certified0923)
  apply certified_cons (by exact certified0924)
  apply certified_cons (by exact certified0924swap)
  apply certified_cons (by exact certified0925)
  apply certified_cons (by exact certified0925swap)
  apply certified_cons (by exact certified0926)
  apply certified_cons (by exact certified0927)
  apply certified_cons (by exact certified0928)
  apply certified_cons (by exact certified0928swap)
  apply certified_cons (by exact certified0929)
  apply certified_cons (by exact certified0929swap)
  apply certified_cons (by exact certified0930)
  apply certified_cons (by exact certified0931)
  apply certified_cons (by exact certified0932)
  apply certified_cons (by exact certified0932swap)
  apply certified_cons (by exact certified0933)
  apply certified_cons (by exact certified0933swap)
  apply certified_cons (by exact certified0934)
  apply certified_cons (by exact certified0935)
  apply certified_cons (by exact certified0936)
  apply certified_cons (by exact certified0936swap)
  apply certified_cons (by exact certified0937)
  apply certified_cons (by exact certified0937swap)
  apply certified_cons (by exact certified0938)
  apply certified_cons (by exact certified0939)
  apply certified_cons (by exact certified0940)
  apply certified_cons (by exact certified0940swap)
  apply certified_cons (by exact certified0941)
  apply certified_cons (by exact certified0941swap)
  apply certified_cons (by exact certified0942)
  apply certified_cons (by exact certified0943)
  apply certified_cons (by exact certified0944)
  apply certified_cons (by exact certified0944swap)
  apply certified_cons (by exact certified0945)
  apply certified_cons (by exact certified0945swap)
  apply certified_cons (by exact certified0946)
  apply certified_cons (by exact certified0947)
  apply certified_cons (by exact certified0948)
  apply certified_cons (by exact certified0948swap)
  apply certified_cons (by exact certified0949)
  apply certified_cons (by exact certified0949swap)
  simp
#print axioms certified_keys18
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
