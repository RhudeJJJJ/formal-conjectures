/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0581 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0581 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0581 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0581_checked : acceptsGraphIso
    (source (graph core0581) (root 7) 0 2) DegreeOneSmallSpectrum433.graph sourceMap0581=true := by decide +kernel
theorem fusedMap0581_checked : acceptsGraphIso
    (fused (graph core0581) (root 7) 0 2) DegreeOneSmallSpectrum434.graph fusedMap0581=true := by decide +kernel
theorem certified0581 : Certified (graph core0581) (root 7) 0 2 :=
  of_native_maps core0581 DegreeOneSmallSpectrum433.graph DegreeOneSmallSpectrum434.graph
    sourceMap0581 fusedMap0581 sourceMap0581_checked fusedMap0581_checked
    DegreeOneSmallComparisons.comparison0581
#print axioms sourceMap0581_checked
#print axioms fusedMap0581_checked
#print axioms certified0581
def sourceMap0581swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0581swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0581swap_checked : acceptsGraphIso
    (source (graph core0581) (root 7) 2 0) DegreeOneSmallSpectrum433.graph sourceMap0581swap=true := by decide +kernel
theorem fusedMap0581swap_checked : acceptsGraphIso
    (fused (graph core0581) (root 7) 2 0) DegreeOneSmallSpectrum434.graph fusedMap0581swap=true := by decide +kernel
theorem certified0581swap : Certified (graph core0581) (root 7) 2 0 :=
  of_native_maps core0581 DegreeOneSmallSpectrum433.graph DegreeOneSmallSpectrum434.graph
    sourceMap0581swap fusedMap0581swap sourceMap0581swap_checked fusedMap0581swap_checked
    DegreeOneSmallComparisons.comparison0581
#print axioms sourceMap0581swap_checked
#print axioms fusedMap0581swap_checked
#print axioms certified0581swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
