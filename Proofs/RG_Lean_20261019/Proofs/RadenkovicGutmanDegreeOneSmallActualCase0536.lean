/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0536 : Family 7 := level7.get ⟨17,by decide⟩
def sourceMap0536 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0536 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0536_checked : acceptsGraphIso
    (source (graph core0536) (root 7) 1 2) DegreeOneSmallSpectrum1486.graph sourceMap0536=true := by decide +kernel
theorem fusedMap0536_checked : acceptsGraphIso
    (fused (graph core0536) (root 7) 1 2) DegreeOneSmallSpectrum951.graph fusedMap0536=true := by decide +kernel
theorem certified0536 : Certified (graph core0536) (root 7) 1 2 :=
  of_native_maps core0536 DegreeOneSmallSpectrum1486.graph DegreeOneSmallSpectrum951.graph
    sourceMap0536 fusedMap0536 sourceMap0536_checked fusedMap0536_checked
    DegreeOneSmallComparisons.comparison0536
#print axioms sourceMap0536_checked
#print axioms fusedMap0536_checked
#print axioms certified0536
def sourceMap0536swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0536swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0536swap_checked : acceptsGraphIso
    (source (graph core0536) (root 7) 2 1) DegreeOneSmallSpectrum1486.graph sourceMap0536swap=true := by decide +kernel
theorem fusedMap0536swap_checked : acceptsGraphIso
    (fused (graph core0536) (root 7) 2 1) DegreeOneSmallSpectrum951.graph fusedMap0536swap=true := by decide +kernel
theorem certified0536swap : Certified (graph core0536) (root 7) 2 1 :=
  of_native_maps core0536 DegreeOneSmallSpectrum1486.graph DegreeOneSmallSpectrum951.graph
    sourceMap0536swap fusedMap0536swap sourceMap0536swap_checked fusedMap0536swap_checked
    DegreeOneSmallComparisons.comparison0536
#print axioms sourceMap0536swap_checked
#print axioms fusedMap0536swap_checked
#print axioms certified0536swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
