/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0225 : Family 9 := level9.get ⟨242,by decide⟩
def sourceMap0225 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0225 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0225_checked : acceptsGraphIso
    (source (graph core0225) (root 9) 0 0) DegreeOneSmallSpectrum639.graph sourceMap0225=true := by decide +kernel
theorem fusedMap0225_checked : acceptsGraphIso
    (fused (graph core0225) (root 9) 0 0) DegreeOneSmallSpectrum538.graph fusedMap0225=true := by decide +kernel
theorem certified0225 : Certified (graph core0225) (root 9) 0 0 :=
  of_native_maps core0225 DegreeOneSmallSpectrum639.graph DegreeOneSmallSpectrum538.graph
    sourceMap0225 fusedMap0225 sourceMap0225_checked fusedMap0225_checked
    DegreeTwoThreeFiniteComparisons.comparison0225
#print axioms sourceMap0225_checked
#print axioms fusedMap0225_checked
#print axioms certified0225
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
