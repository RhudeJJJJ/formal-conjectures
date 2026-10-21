/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0638 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0638 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0638 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0638_checked : acceptsGraphIso
    (source (graph core0638) (root 7) 1 2) DegreeOneSmallSpectrum1411.graph sourceMap0638=true := by decide +kernel
theorem fusedMap0638_checked : acceptsGraphIso
    (fused (graph core0638) (root 7) 1 2) DegreeOneSmallSpectrum923.graph fusedMap0638=true := by decide +kernel
theorem certified0638 : Certified (graph core0638) (root 7) 1 2 :=
  of_native_maps core0638 DegreeOneSmallSpectrum1411.graph DegreeOneSmallSpectrum923.graph
    sourceMap0638 fusedMap0638 sourceMap0638_checked fusedMap0638_checked
    DegreeOneSmallComparisons.comparison0638
#print axioms sourceMap0638_checked
#print axioms fusedMap0638_checked
#print axioms certified0638
def sourceMap0638swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0638swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0638swap_checked : acceptsGraphIso
    (source (graph core0638) (root 7) 2 1) DegreeOneSmallSpectrum1411.graph sourceMap0638swap=true := by decide +kernel
theorem fusedMap0638swap_checked : acceptsGraphIso
    (fused (graph core0638) (root 7) 2 1) DegreeOneSmallSpectrum923.graph fusedMap0638swap=true := by decide +kernel
theorem certified0638swap : Certified (graph core0638) (root 7) 2 1 :=
  of_native_maps core0638 DegreeOneSmallSpectrum1411.graph DegreeOneSmallSpectrum923.graph
    sourceMap0638swap fusedMap0638swap sourceMap0638swap_checked fusedMap0638swap_checked
    DegreeOneSmallComparisons.comparison0638
#print axioms sourceMap0638swap_checked
#print axioms fusedMap0638swap_checked
#print axioms certified0638swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
