/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0098 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap0098 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0098 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,8,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap0098_checked : acceptsGraphIso
    (source (graph core0098) (root 8) 0 0) DegreeOneSmallSpectrum247.graph sourceMap0098=true := by decide +kernel
theorem fusedMap0098_checked : acceptsGraphIso
    (fused (graph core0098) (root 8) 0 0) DegreeOneSmallSpectrum310.graph fusedMap0098=true := by decide +kernel
theorem certified0098 : Certified (graph core0098) (root 8) 0 0 :=
  of_native_maps core0098 DegreeOneSmallSpectrum247.graph DegreeOneSmallSpectrum310.graph
    sourceMap0098 fusedMap0098 sourceMap0098_checked fusedMap0098_checked
    DegreeTwoThreeFiniteComparisons.comparison0098
#print axioms sourceMap0098_checked
#print axioms fusedMap0098_checked
#print axioms certified0098
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
