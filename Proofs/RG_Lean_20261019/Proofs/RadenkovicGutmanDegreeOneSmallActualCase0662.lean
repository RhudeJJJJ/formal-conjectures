/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0662 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0662 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0662 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0662_checked : acceptsGraphIso
    (source (graph core0662) (root 7) 1 2) DegreeOneSmallSpectrum1482.graph sourceMap0662=true := by decide +kernel
theorem fusedMap0662_checked : acceptsGraphIso
    (fused (graph core0662) (root 7) 1 2) DegreeOneSmallSpectrum947.graph fusedMap0662=true := by decide +kernel
theorem certified0662 : Certified (graph core0662) (root 7) 1 2 :=
  of_native_maps core0662 DegreeOneSmallSpectrum1482.graph DegreeOneSmallSpectrum947.graph
    sourceMap0662 fusedMap0662 sourceMap0662_checked fusedMap0662_checked
    DegreeOneSmallComparisons.comparison0662
#print axioms sourceMap0662_checked
#print axioms fusedMap0662_checked
#print axioms certified0662
def sourceMap0662swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0662swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0662swap_checked : acceptsGraphIso
    (source (graph core0662) (root 7) 2 1) DegreeOneSmallSpectrum1482.graph sourceMap0662swap=true := by decide +kernel
theorem fusedMap0662swap_checked : acceptsGraphIso
    (fused (graph core0662) (root 7) 2 1) DegreeOneSmallSpectrum947.graph fusedMap0662swap=true := by decide +kernel
theorem certified0662swap : Certified (graph core0662) (root 7) 2 1 :=
  of_native_maps core0662 DegreeOneSmallSpectrum1482.graph DegreeOneSmallSpectrum947.graph
    sourceMap0662swap fusedMap0662swap sourceMap0662swap_checked fusedMap0662swap_checked
    DegreeOneSmallComparisons.comparison0662
#print axioms sourceMap0662swap_checked
#print axioms fusedMap0662swap_checked
#print axioms certified0662swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
