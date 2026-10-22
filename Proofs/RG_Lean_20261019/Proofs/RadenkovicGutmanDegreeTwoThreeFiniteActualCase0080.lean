/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0080 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap0080 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0080 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0080_checked : acceptsGraphIso
    (source (graph core0080) (root 8) 0 0) DegreeOneSmallSpectrum205.graph sourceMap0080=true := by decide +kernel
theorem fusedMap0080_checked : acceptsGraphIso
    (fused (graph core0080) (root 8) 0 0) DegreeOneSmallSpectrum200.graph fusedMap0080=true := by decide +kernel
theorem certified0080 : Certified (graph core0080) (root 8) 0 0 :=
  of_native_maps core0080 DegreeOneSmallSpectrum205.graph DegreeOneSmallSpectrum200.graph
    sourceMap0080 fusedMap0080 sourceMap0080_checked fusedMap0080_checked
    DegreeTwoThreeFiniteComparisons.comparison0080
#print axioms sourceMap0080_checked
#print axioms fusedMap0080_checked
#print axioms certified0080
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
