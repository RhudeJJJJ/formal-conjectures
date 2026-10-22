/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0155 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap0155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap0155 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap0155_checked : acceptsGraphIso
    (source (graph core0155) (root 8) 0 0) DegreeOneSmallSpectrum236.graph sourceMap0155=true := by decide +kernel
theorem fusedMap0155_checked : acceptsGraphIso
    (fused (graph core0155) (root 8) 0 0) DegreeOneSmallSpectrum235.graph fusedMap0155=true := by decide +kernel
theorem certified0155 : Certified (graph core0155) (root 8) 0 0 :=
  of_native_maps core0155 DegreeOneSmallSpectrum236.graph DegreeOneSmallSpectrum235.graph
    sourceMap0155 fusedMap0155 sourceMap0155_checked fusedMap0155_checked
    DegreeTwoThreeFiniteComparisons.comparison0155
#print axioms sourceMap0155_checked
#print axioms fusedMap0155_checked
#print axioms certified0155
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
