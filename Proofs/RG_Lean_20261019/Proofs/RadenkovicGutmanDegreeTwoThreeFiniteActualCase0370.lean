/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0370 : Family 9 := level9.get ⟨602,by decide⟩
def sourceMap0370 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0370 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0370_checked : acceptsGraphIso
    (source (graph core0370) (root 9) 0 0) DegreeOneSmallSpectrum716.graph sourceMap0370=true := by decide +kernel
theorem fusedMap0370_checked : acceptsGraphIso
    (fused (graph core0370) (root 9) 0 0) DegreeOneSmallSpectrum715.graph fusedMap0370=true := by decide +kernel
theorem certified0370 : Certified (graph core0370) (root 9) 0 0 :=
  of_native_maps core0370 DegreeOneSmallSpectrum716.graph DegreeOneSmallSpectrum715.graph
    sourceMap0370 fusedMap0370 sourceMap0370_checked fusedMap0370_checked
    DegreeTwoThreeFiniteComparisons.comparison0370
#print axioms sourceMap0370_checked
#print axioms fusedMap0370_checked
#print axioms certified0370
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
