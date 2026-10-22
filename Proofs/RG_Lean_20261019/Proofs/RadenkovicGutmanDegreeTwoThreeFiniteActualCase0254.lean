/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0254 : Family 9 := level9.get ⟨312,by decide⟩
def sourceMap0254 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0254 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0254_checked : acceptsGraphIso
    (source (graph core0254) (root 9) 0 0) DegreeOneSmallSpectrum406.graph sourceMap0254=true := by decide +kernel
theorem fusedMap0254_checked : acceptsGraphIso
    (fused (graph core0254) (root 9) 0 0) DegreeOneSmallSpectrum405.graph fusedMap0254=true := by decide +kernel
theorem certified0254 : Certified (graph core0254) (root 9) 0 0 :=
  of_native_maps core0254 DegreeOneSmallSpectrum406.graph DegreeOneSmallSpectrum405.graph
    sourceMap0254 fusedMap0254 sourceMap0254_checked fusedMap0254_checked
    DegreeTwoThreeFiniteComparisons.comparison0254
#print axioms sourceMap0254_checked
#print axioms fusedMap0254_checked
#print axioms certified0254
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
