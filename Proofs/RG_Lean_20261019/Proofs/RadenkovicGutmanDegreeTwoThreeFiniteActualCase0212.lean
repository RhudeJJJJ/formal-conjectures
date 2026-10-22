/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0212 : Family 9 := level9.get ⟨196,by decide⟩
def sourceMap0212 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0212 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0212_checked : acceptsGraphIso
    (source (graph core0212) (root 9) 0 0) DegreeOneSmallSpectrum437.graph sourceMap0212=true := by decide +kernel
theorem fusedMap0212_checked : acceptsGraphIso
    (fused (graph core0212) (root 9) 0 0) DegreeOneSmallSpectrum431.graph fusedMap0212=true := by decide +kernel
theorem certified0212 : Certified (graph core0212) (root 9) 0 0 :=
  of_native_maps core0212 DegreeOneSmallSpectrum437.graph DegreeOneSmallSpectrum431.graph
    sourceMap0212 fusedMap0212 sourceMap0212_checked fusedMap0212_checked
    DegreeTwoThreeFiniteComparisons.comparison0212
#print axioms sourceMap0212_checked
#print axioms fusedMap0212_checked
#print axioms certified0212
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
