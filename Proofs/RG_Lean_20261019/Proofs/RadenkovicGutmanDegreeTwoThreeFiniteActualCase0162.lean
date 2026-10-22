/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0162 : Family 9 := level9.get ⟨22,by decide⟩
def sourceMap0162 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0162 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0162_checked : acceptsGraphIso
    (source (graph core0162) (root 9) 0 0) DegreeOneSmallSpectrum423.graph sourceMap0162=true := by decide +kernel
theorem fusedMap0162_checked : acceptsGraphIso
    (fused (graph core0162) (root 9) 0 0) DegreeOneSmallSpectrum383.graph fusedMap0162=true := by decide +kernel
theorem certified0162 : Certified (graph core0162) (root 9) 0 0 :=
  of_native_maps core0162 DegreeOneSmallSpectrum423.graph DegreeOneSmallSpectrum383.graph
    sourceMap0162 fusedMap0162 sourceMap0162_checked fusedMap0162_checked
    DegreeTwoThreeFiniteComparisons.comparison0162
#print axioms sourceMap0162_checked
#print axioms fusedMap0162_checked
#print axioms certified0162
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
