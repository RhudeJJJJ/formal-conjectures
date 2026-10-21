/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0602 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0602 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0602 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0602_checked : acceptsGraphIso
    (source (graph core0602) (root 7) 1 2) DegreeOneSmallSpectrum1208.graph sourceMap0602=true := by decide +kernel
theorem fusedMap0602_checked : acceptsGraphIso
    (fused (graph core0602) (root 7) 1 2) DegreeOneSmallSpectrum880.graph fusedMap0602=true := by decide +kernel
theorem certified0602 : Certified (graph core0602) (root 7) 1 2 :=
  of_native_maps core0602 DegreeOneSmallSpectrum1208.graph DegreeOneSmallSpectrum880.graph
    sourceMap0602 fusedMap0602 sourceMap0602_checked fusedMap0602_checked
    DegreeOneSmallComparisons.comparison0602
#print axioms sourceMap0602_checked
#print axioms fusedMap0602_checked
#print axioms certified0602
def sourceMap0602swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0602swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0602swap_checked : acceptsGraphIso
    (source (graph core0602) (root 7) 2 1) DegreeOneSmallSpectrum1208.graph sourceMap0602swap=true := by decide +kernel
theorem fusedMap0602swap_checked : acceptsGraphIso
    (fused (graph core0602) (root 7) 2 1) DegreeOneSmallSpectrum880.graph fusedMap0602swap=true := by decide +kernel
theorem certified0602swap : Certified (graph core0602) (root 7) 2 1 :=
  of_native_maps core0602 DegreeOneSmallSpectrum1208.graph DegreeOneSmallSpectrum880.graph
    sourceMap0602swap fusedMap0602swap sourceMap0602swap_checked fusedMap0602swap_checked
    DegreeOneSmallComparisons.comparison0602
#print axioms sourceMap0602swap_checked
#print axioms fusedMap0602swap_checked
#print axioms certified0602swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
