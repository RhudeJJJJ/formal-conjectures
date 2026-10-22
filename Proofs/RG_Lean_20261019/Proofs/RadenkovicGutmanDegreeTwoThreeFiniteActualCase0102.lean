/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0102 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap0102 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0102 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0102_checked : acceptsGraphIso
    (source (graph core0102) (root 8) 0 0) DegreeOneSmallSpectrum287.graph sourceMap0102=true := by decide +kernel
theorem fusedMap0102_checked : acceptsGraphIso
    (fused (graph core0102) (root 8) 0 0) DegreeOneSmallSpectrum277.graph fusedMap0102=true := by decide +kernel
theorem certified0102 : Certified (graph core0102) (root 8) 0 0 :=
  of_native_maps core0102 DegreeOneSmallSpectrum287.graph DegreeOneSmallSpectrum277.graph
    sourceMap0102 fusedMap0102 sourceMap0102_checked fusedMap0102_checked
    DegreeTwoThreeFiniteComparisons.comparison0102
#print axioms sourceMap0102_checked
#print axioms fusedMap0102_checked
#print axioms certified0102
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
