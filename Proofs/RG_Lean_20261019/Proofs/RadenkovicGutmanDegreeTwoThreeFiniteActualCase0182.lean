/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0182 : Family 9 := level9.get ⟨106,by decide⟩
def sourceMap0182 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0182 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0182_checked : acceptsGraphIso
    (source (graph core0182) (root 9) 0 0) DegreeOneSmallSpectrum416.graph sourceMap0182=true := by decide +kernel
theorem fusedMap0182_checked : acceptsGraphIso
    (fused (graph core0182) (root 9) 0 0) DegreeOneSmallSpectrum558.graph fusedMap0182=true := by decide +kernel
theorem certified0182 : Certified (graph core0182) (root 9) 0 0 :=
  of_native_maps core0182 DegreeOneSmallSpectrum416.graph DegreeOneSmallSpectrum558.graph
    sourceMap0182 fusedMap0182 sourceMap0182_checked fusedMap0182_checked
    DegreeTwoThreeFiniteComparisons.comparison0182
#print axioms sourceMap0182_checked
#print axioms fusedMap0182_checked
#print axioms certified0182
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
