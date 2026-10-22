/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0193 : Family 9 := level9.get ⟨134,by decide⟩
def sourceMap0193 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0193 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0193_checked : acceptsGraphIso
    (source (graph core0193) (root 9) 0 0) DegreeOneSmallSpectrum440.graph sourceMap0193=true := by decide +kernel
theorem fusedMap0193_checked : acceptsGraphIso
    (fused (graph core0193) (root 9) 0 0) DegreeOneSmallSpectrum434.graph fusedMap0193=true := by decide +kernel
theorem certified0193 : Certified (graph core0193) (root 9) 0 0 :=
  of_native_maps core0193 DegreeOneSmallSpectrum440.graph DegreeOneSmallSpectrum434.graph
    sourceMap0193 fusedMap0193 sourceMap0193_checked fusedMap0193_checked
    DegreeTwoThreeFiniteComparisons.comparison0193
#print axioms sourceMap0193_checked
#print axioms fusedMap0193_checked
#print axioms certified0193
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
