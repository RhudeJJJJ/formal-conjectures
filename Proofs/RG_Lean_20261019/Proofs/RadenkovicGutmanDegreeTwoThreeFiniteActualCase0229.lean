/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0229 : Family 9 := level9.get ⟨248,by decide⟩
def sourceMap0229 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0229 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0229_checked : acceptsGraphIso
    (source (graph core0229) (root 9) 0 0) DegreeOneSmallSpectrum438.graph sourceMap0229=true := by decide +kernel
theorem fusedMap0229_checked : acceptsGraphIso
    (fused (graph core0229) (root 9) 0 0) DegreeOneSmallSpectrum432.graph fusedMap0229=true := by decide +kernel
theorem certified0229 : Certified (graph core0229) (root 9) 0 0 :=
  of_native_maps core0229 DegreeOneSmallSpectrum438.graph DegreeOneSmallSpectrum432.graph
    sourceMap0229 fusedMap0229 sourceMap0229_checked fusedMap0229_checked
    DegreeTwoThreeFiniteComparisons.comparison0229
#print axioms sourceMap0229_checked
#print axioms fusedMap0229_checked
#print axioms certified0229
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
