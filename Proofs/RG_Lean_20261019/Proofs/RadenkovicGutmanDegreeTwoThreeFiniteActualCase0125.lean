/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0125 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap0125 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap0125 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap0125_checked : acceptsGraphIso
    (source (graph core0125) (root 8) 0 0) DegreeOneSmallSpectrum253.graph sourceMap0125=true := by decide +kernel
theorem fusedMap0125_checked : acceptsGraphIso
    (fused (graph core0125) (root 8) 0 0) DegreeOneSmallSpectrum249.graph fusedMap0125=true := by decide +kernel
theorem certified0125 : Certified (graph core0125) (root 8) 0 0 :=
  of_native_maps core0125 DegreeOneSmallSpectrum253.graph DegreeOneSmallSpectrum249.graph
    sourceMap0125 fusedMap0125 sourceMap0125_checked fusedMap0125_checked
    DegreeTwoThreeFiniteComparisons.comparison0125
#print axioms sourceMap0125_checked
#print axioms fusedMap0125_checked
#print axioms certified0125
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
