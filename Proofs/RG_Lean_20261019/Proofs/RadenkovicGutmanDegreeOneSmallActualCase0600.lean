/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0600 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0600 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0600 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0600_checked : acceptsGraphIso
    (source (graph core0600) (root 7) 0 3) DegreeOneSmallSpectrum1211.graph sourceMap0600=true := by decide +kernel
theorem fusedMap0600_checked : acceptsGraphIso
    (fused (graph core0600) (root 7) 0 3) DegreeOneSmallSpectrum880.graph fusedMap0600=true := by decide +kernel
theorem certified0600 : Certified (graph core0600) (root 7) 0 3 :=
  of_native_maps core0600 DegreeOneSmallSpectrum1211.graph DegreeOneSmallSpectrum880.graph
    sourceMap0600 fusedMap0600 sourceMap0600_checked fusedMap0600_checked
    DegreeOneSmallComparisons.comparison0600
#print axioms sourceMap0600_checked
#print axioms fusedMap0600_checked
#print axioms certified0600
def sourceMap0600swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0600swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0600swap_checked : acceptsGraphIso
    (source (graph core0600) (root 7) 3 0) DegreeOneSmallSpectrum1211.graph sourceMap0600swap=true := by decide +kernel
theorem fusedMap0600swap_checked : acceptsGraphIso
    (fused (graph core0600) (root 7) 3 0) DegreeOneSmallSpectrum880.graph fusedMap0600swap=true := by decide +kernel
theorem certified0600swap : Certified (graph core0600) (root 7) 3 0 :=
  of_native_maps core0600 DegreeOneSmallSpectrum1211.graph DegreeOneSmallSpectrum880.graph
    sourceMap0600swap fusedMap0600swap sourceMap0600swap_checked fusedMap0600swap_checked
    DegreeOneSmallComparisons.comparison0600
#print axioms sourceMap0600swap_checked
#print axioms fusedMap0600swap_checked
#print axioms certified0600swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
