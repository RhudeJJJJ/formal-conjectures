/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0900
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0901
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0902
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0903
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0904
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0905
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0906
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0907
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0908
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0909
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0910
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0911
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0912
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0913
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0914
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0915
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0916
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0917
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0918
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0919
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0920
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0921
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0922
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0923
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0924
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0925
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0926
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0927
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0928
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0929
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0930
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0931
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0932
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0933
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0934
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0935
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0936
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0937
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0938
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0939
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0940
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0941
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0942
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0943
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0944
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0945
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0946
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0947
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0948
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0949
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys018 : ∀ k ∈ keys018, Certified k := by
  apply certified_cons (by exact certified0900)
  apply certified_cons (by exact certified0901)
  apply certified_cons (by exact certified0902)
  apply certified_cons (by exact certified0903)
  apply certified_cons (by exact certified0904)
  apply certified_cons (by exact certified0905)
  apply certified_cons (by exact certified0906)
  apply certified_cons (by exact certified0907)
  apply certified_cons (by exact certified0908)
  apply certified_cons (by exact certified0909)
  apply certified_cons (by exact certified0910)
  apply certified_cons (by exact certified0911)
  apply certified_cons (by exact certified0912)
  apply certified_cons (by exact certified0913)
  apply certified_cons (by exact certified0914)
  apply certified_cons (by exact certified0915)
  apply certified_cons (by exact certified0916)
  apply certified_cons (by exact certified0917)
  apply certified_cons (by exact certified0918)
  apply certified_cons (by exact certified0919)
  apply certified_cons (by exact certified0920)
  apply certified_cons (by exact certified0921)
  apply certified_cons (by exact certified0922)
  apply certified_cons (by exact certified0923)
  apply certified_cons (by exact certified0924)
  apply certified_cons (by exact certified0925)
  apply certified_cons (by exact certified0926)
  apply certified_cons (by exact certified0927)
  apply certified_cons (by exact certified0928)
  apply certified_cons (by exact certified0929)
  apply certified_cons (by exact certified0930)
  apply certified_cons (by exact certified0931)
  apply certified_cons (by exact certified0932)
  apply certified_cons (by exact certified0933)
  apply certified_cons (by exact certified0934)
  apply certified_cons (by exact certified0935)
  apply certified_cons (by exact certified0936)
  apply certified_cons (by exact certified0937)
  apply certified_cons (by exact certified0938)
  apply certified_cons (by exact certified0939)
  apply certified_cons (by exact certified0940)
  apply certified_cons (by exact certified0941)
  apply certified_cons (by exact certified0942)
  apply certified_cons (by exact certified0943)
  apply certified_cons (by exact certified0944)
  apply certified_cons (by exact certified0945)
  apply certified_cons (by exact certified0946)
  apply certified_cons (by exact certified0947)
  apply certified_cons (by exact certified0948)
  apply certified_cons (by exact certified0949)
  simp
#print axioms certified_keys018
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
