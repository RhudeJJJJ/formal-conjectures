/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0065 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap0065 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0065 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0065_checked : acceptsGraphIso
    (source (graph core0065) (root 8) 0 0) DegreeOneSmallSpectrum172.graph sourceMap0065=true := by decide +kernel
theorem fusedMap0065_checked : acceptsGraphIso
    (fused (graph core0065) (root 8) 0 0) DegreeOneSmallSpectrum193.graph fusedMap0065=true := by decide +kernel
theorem certified0065 : Certified (graph core0065) (root 8) 0 0 :=
  of_native_maps core0065 DegreeOneSmallSpectrum172.graph DegreeOneSmallSpectrum193.graph
    sourceMap0065 fusedMap0065 sourceMap0065_checked fusedMap0065_checked
    DegreeTwoThreeFiniteComparisons.comparison0065
#print axioms sourceMap0065_checked
#print axioms fusedMap0065_checked
#print axioms certified0065
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
