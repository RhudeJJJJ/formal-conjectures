/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0204 : Family 9 := level9.get ⟨178,by decide⟩
def sourceMap0204 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0204 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0204_checked : acceptsGraphIso
    (source (graph core0204) (root 9) 0 0) DegreeOneSmallSpectrum664.graph sourceMap0204=true := by decide +kernel
theorem fusedMap0204_checked : acceptsGraphIso
    (fused (graph core0204) (root 9) 0 0) DegreeOneSmallSpectrum462.graph fusedMap0204=true := by decide +kernel
theorem certified0204 : Certified (graph core0204) (root 9) 0 0 :=
  of_native_maps core0204 DegreeOneSmallSpectrum664.graph DegreeOneSmallSpectrum462.graph
    sourceMap0204 fusedMap0204 sourceMap0204_checked fusedMap0204_checked
    DegreeTwoThreeFiniteComparisons.comparison0204
#print axioms sourceMap0204_checked
#print axioms fusedMap0204_checked
#print axioms certified0204
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
