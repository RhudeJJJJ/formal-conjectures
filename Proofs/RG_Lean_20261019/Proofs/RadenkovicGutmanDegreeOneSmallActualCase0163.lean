/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0163 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0163 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,11,6,7,8,9,10] (sourceLabel 5 0 4 v)
def fusedMap0163 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0163_checked : acceptsGraphIso
    (source (graph core0163) (root 5) 0 4) DegreeOneSmallSpectrum397.graph sourceMap0163=true := by decide +kernel
theorem fusedMap0163_checked : acceptsGraphIso
    (fused (graph core0163) (root 5) 0 4) DegreeOneSmallSpectrum369.graph fusedMap0163=true := by decide +kernel
theorem certified0163 : Certified (graph core0163) (root 5) 0 4 :=
  of_native_maps core0163 DegreeOneSmallSpectrum397.graph DegreeOneSmallSpectrum369.graph
    sourceMap0163 fusedMap0163 sourceMap0163_checked fusedMap0163_checked
    DegreeOneSmallComparisons.comparison0163
#print axioms sourceMap0163_checked
#print axioms fusedMap0163_checked
#print axioms certified0163
def sourceMap0163swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 4 0 v)
def fusedMap0163swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0163swap_checked : acceptsGraphIso
    (source (graph core0163) (root 5) 4 0) DegreeOneSmallSpectrum397.graph sourceMap0163swap=true := by decide +kernel
theorem fusedMap0163swap_checked : acceptsGraphIso
    (fused (graph core0163) (root 5) 4 0) DegreeOneSmallSpectrum369.graph fusedMap0163swap=true := by decide +kernel
theorem certified0163swap : Certified (graph core0163) (root 5) 4 0 :=
  of_native_maps core0163 DegreeOneSmallSpectrum397.graph DegreeOneSmallSpectrum369.graph
    sourceMap0163swap fusedMap0163swap sourceMap0163swap_checked fusedMap0163swap_checked
    DegreeOneSmallComparisons.comparison0163
#print axioms sourceMap0163swap_checked
#print axioms fusedMap0163swap_checked
#print axioms certified0163swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
