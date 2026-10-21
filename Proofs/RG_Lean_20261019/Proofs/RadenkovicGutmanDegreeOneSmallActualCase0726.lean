/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0726 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0726 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0726 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0726_checked : acceptsGraphIso
    (source (graph core0726) (root 7) 0 3) DegreeOneSmallSpectrum1350.graph sourceMap0726=true := by decide +kernel
theorem fusedMap0726_checked : acceptsGraphIso
    (fused (graph core0726) (root 7) 0 3) DegreeOneSmallSpectrum1353.graph fusedMap0726=true := by decide +kernel
theorem certified0726 : Certified (graph core0726) (root 7) 0 3 :=
  of_native_maps core0726 DegreeOneSmallSpectrum1350.graph DegreeOneSmallSpectrum1353.graph
    sourceMap0726 fusedMap0726 sourceMap0726_checked fusedMap0726_checked
    DegreeOneSmallComparisons.comparison0726
#print axioms sourceMap0726_checked
#print axioms fusedMap0726_checked
#print axioms certified0726
def sourceMap0726swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0726swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0726swap_checked : acceptsGraphIso
    (source (graph core0726) (root 7) 3 0) DegreeOneSmallSpectrum1350.graph sourceMap0726swap=true := by decide +kernel
theorem fusedMap0726swap_checked : acceptsGraphIso
    (fused (graph core0726) (root 7) 3 0) DegreeOneSmallSpectrum1353.graph fusedMap0726swap=true := by decide +kernel
theorem certified0726swap : Certified (graph core0726) (root 7) 3 0 :=
  of_native_maps core0726 DegreeOneSmallSpectrum1350.graph DegreeOneSmallSpectrum1353.graph
    sourceMap0726swap fusedMap0726swap sourceMap0726swap_checked fusedMap0726swap_checked
    DegreeOneSmallComparisons.comparison0726
#print axioms sourceMap0726swap_checked
#print axioms fusedMap0726swap_checked
#print axioms certified0726swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
