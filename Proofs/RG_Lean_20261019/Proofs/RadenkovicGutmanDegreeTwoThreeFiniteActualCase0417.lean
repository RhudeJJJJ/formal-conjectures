/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0417 : Family 10 := level10.get ⟨104,by decide⟩
def sourceMap0417 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0417 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0417_checked : acceptsGraphIso
    (source (graph core0417) (root 10) 0 0) DegreeOneSmallSpectrum1072.graph sourceMap0417=true := by decide +kernel
theorem fusedMap0417_checked : acceptsGraphIso
    (fused (graph core0417) (root 10) 0 0) DegreeOneSmallSpectrum926.graph fusedMap0417=true := by decide +kernel
theorem certified0417 : Certified (graph core0417) (root 10) 0 0 :=
  of_native_maps core0417 DegreeOneSmallSpectrum1072.graph DegreeOneSmallSpectrum926.graph
    sourceMap0417 fusedMap0417 sourceMap0417_checked fusedMap0417_checked
    DegreeTwoThreeFiniteComparisons.comparison0417
#print axioms sourceMap0417_checked
#print axioms fusedMap0417_checked
#print axioms certified0417
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
