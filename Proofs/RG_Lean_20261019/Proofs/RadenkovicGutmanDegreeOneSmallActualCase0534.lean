/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0534 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0534 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0534 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0534_checked : acceptsGraphIso
    (source (graph core0534) (root 7) 0 3) DegreeOneSmallSpectrum950.graph sourceMap0534=true := by decide +kernel
theorem fusedMap0534_checked : acceptsGraphIso
    (fused (graph core0534) (root 7) 0 3) DegreeOneSmallSpectrum951.graph fusedMap0534=true := by decide +kernel
theorem certified0534 : Certified (graph core0534) (root 7) 0 3 :=
  of_native_maps core0534 DegreeOneSmallSpectrum950.graph DegreeOneSmallSpectrum951.graph
    sourceMap0534 fusedMap0534 sourceMap0534_checked fusedMap0534_checked
    DegreeOneSmallComparisons.comparison0534
#print axioms sourceMap0534_checked
#print axioms fusedMap0534_checked
#print axioms certified0534
def sourceMap0534swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0534swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0534swap_checked : acceptsGraphIso
    (source (graph core0534) (root 7) 3 0) DegreeOneSmallSpectrum950.graph sourceMap0534swap=true := by decide +kernel
theorem fusedMap0534swap_checked : acceptsGraphIso
    (fused (graph core0534) (root 7) 3 0) DegreeOneSmallSpectrum951.graph fusedMap0534swap=true := by decide +kernel
theorem certified0534swap : Certified (graph core0534) (root 7) 3 0 :=
  of_native_maps core0534 DegreeOneSmallSpectrum950.graph DegreeOneSmallSpectrum951.graph
    sourceMap0534swap fusedMap0534swap sourceMap0534swap_checked fusedMap0534swap_checked
    DegreeOneSmallComparisons.comparison0534
#print axioms sourceMap0534swap_checked
#print axioms fusedMap0534swap_checked
#print axioms certified0534swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
