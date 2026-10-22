/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0308 : Family 9 := level9.get ⟨455,by decide⟩
def sourceMap0308 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0308 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0308_checked : acceptsGraphIso
    (source (graph core0308) (root 9) 0 0) DegreeOneSmallSpectrum725.graph sourceMap0308=true := by decide +kernel
theorem fusedMap0308_checked : acceptsGraphIso
    (fused (graph core0308) (root 9) 0 0) DegreeOneSmallSpectrum705.graph fusedMap0308=true := by decide +kernel
theorem certified0308 : Certified (graph core0308) (root 9) 0 0 :=
  of_native_maps core0308 DegreeOneSmallSpectrum725.graph DegreeOneSmallSpectrum705.graph
    sourceMap0308 fusedMap0308 sourceMap0308_checked fusedMap0308_checked
    DegreeTwoThreeFiniteComparisons.comparison0308
#print axioms sourceMap0308_checked
#print axioms fusedMap0308_checked
#print axioms certified0308
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
