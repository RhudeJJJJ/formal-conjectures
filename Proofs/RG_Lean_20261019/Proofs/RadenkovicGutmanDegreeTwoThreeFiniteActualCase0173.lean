/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0173 : Family 9 := level9.get ⟨67,by decide⟩
def sourceMap0173 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0173 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0173_checked : acceptsGraphIso
    (source (graph core0173) (root 9) 0 0) DegreeOneSmallSpectrum486.graph sourceMap0173=true := by decide +kernel
theorem fusedMap0173_checked : acceptsGraphIso
    (fused (graph core0173) (root 9) 0 0) DegreeOneSmallSpectrum483.graph fusedMap0173=true := by decide +kernel
theorem certified0173 : Certified (graph core0173) (root 9) 0 0 :=
  of_native_maps core0173 DegreeOneSmallSpectrum486.graph DegreeOneSmallSpectrum483.graph
    sourceMap0173 fusedMap0173 sourceMap0173_checked fusedMap0173_checked
    DegreeTwoThreeFiniteComparisons.comparison0173
#print axioms sourceMap0173_checked
#print axioms fusedMap0173_checked
#print axioms certified0173
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
