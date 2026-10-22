/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0168 : Family 9 := level9.get ⟨48,by decide⟩
def sourceMap0168 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0168 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0168_checked : acceptsGraphIso
    (source (graph core0168) (root 9) 0 0) DegreeTwoThreeSpectrum365.graph sourceMap0168=true := by decide +kernel
theorem fusedMap0168_checked : acceptsGraphIso
    (fused (graph core0168) (root 9) 0 0) DegreeOneSmallSpectrum423.graph fusedMap0168=true := by decide +kernel
theorem certified0168 : Certified (graph core0168) (root 9) 0 0 :=
  of_native_maps core0168 DegreeTwoThreeSpectrum365.graph DegreeOneSmallSpectrum423.graph
    sourceMap0168 fusedMap0168 sourceMap0168_checked fusedMap0168_checked
    DegreeTwoThreeFiniteComparisons.comparison0168
#print axioms sourceMap0168_checked
#print axioms fusedMap0168_checked
#print axioms certified0168
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
