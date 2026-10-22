/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0190 : Family 9 := level9.get ⟨130,by decide⟩
def sourceMap0190 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0190 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0190_checked : acceptsGraphIso
    (source (graph core0190) (root 9) 0 0) DegreeOneSmallSpectrum406.graph sourceMap0190=true := by decide +kernel
theorem fusedMap0190_checked : acceptsGraphIso
    (fused (graph core0190) (root 9) 0 0) DegreeOneSmallSpectrum544.graph fusedMap0190=true := by decide +kernel
theorem certified0190 : Certified (graph core0190) (root 9) 0 0 :=
  of_native_maps core0190 DegreeOneSmallSpectrum406.graph DegreeOneSmallSpectrum544.graph
    sourceMap0190 fusedMap0190 sourceMap0190_checked fusedMap0190_checked
    DegreeTwoThreeFiniteComparisons.comparison0190
#print axioms sourceMap0190_checked
#print axioms fusedMap0190_checked
#print axioms certified0190
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
