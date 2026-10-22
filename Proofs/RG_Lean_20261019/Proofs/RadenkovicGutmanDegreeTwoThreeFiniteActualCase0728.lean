/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0728 : Family 10 := level10.get ⟨1029,by decide⟩
def sourceMap0728 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0728 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0728_checked : acceptsGraphIso
    (source (graph core0728) (root 10) 0 0) DegreeOneSmallSpectrum1590.graph sourceMap0728=true := by decide +kernel
theorem fusedMap0728_checked : acceptsGraphIso
    (fused (graph core0728) (root 10) 0 0) DegreeOneSmallSpectrum1588.graph fusedMap0728=true := by decide +kernel
theorem certified0728 : Certified (graph core0728) (root 10) 0 0 :=
  of_native_maps core0728 DegreeOneSmallSpectrum1590.graph DegreeOneSmallSpectrum1588.graph
    sourceMap0728 fusedMap0728 sourceMap0728_checked fusedMap0728_checked
    DegreeTwoThreeFiniteComparisons.comparison0728
#print axioms sourceMap0728_checked
#print axioms fusedMap0728_checked
#print axioms certified0728
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
