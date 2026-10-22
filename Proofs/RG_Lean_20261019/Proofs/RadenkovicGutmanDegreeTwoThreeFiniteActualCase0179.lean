/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0179 : Family 9 := level9.get ⟨91,by decide⟩
def sourceMap0179 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0179 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0179_checked : acceptsGraphIso
    (source (graph core0179) (root 9) 0 0) DegreeOneSmallSpectrum530.graph sourceMap0179=true := by decide +kernel
theorem fusedMap0179_checked : acceptsGraphIso
    (fused (graph core0179) (root 9) 0 0) DegreeOneSmallSpectrum514.graph fusedMap0179=true := by decide +kernel
theorem certified0179 : Certified (graph core0179) (root 9) 0 0 :=
  of_native_maps core0179 DegreeOneSmallSpectrum530.graph DegreeOneSmallSpectrum514.graph
    sourceMap0179 fusedMap0179 sourceMap0179_checked fusedMap0179_checked
    DegreeTwoThreeFiniteComparisons.comparison0179
#print axioms sourceMap0179_checked
#print axioms fusedMap0179_checked
#print axioms certified0179
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
