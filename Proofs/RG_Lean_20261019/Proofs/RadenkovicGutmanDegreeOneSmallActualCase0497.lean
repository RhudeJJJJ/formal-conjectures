/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0497 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0497 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0497 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0497_checked : acceptsGraphIso
    (source (graph core0497) (root 7) 0 2) DegreeOneSmallSpectrum478.graph sourceMap0497=true := by decide +kernel
theorem fusedMap0497_checked : acceptsGraphIso
    (fused (graph core0497) (root 7) 0 2) DegreeOneSmallSpectrum372.graph fusedMap0497=true := by decide +kernel
theorem certified0497 : Certified (graph core0497) (root 7) 0 2 :=
  of_native_maps core0497 DegreeOneSmallSpectrum478.graph DegreeOneSmallSpectrum372.graph
    sourceMap0497 fusedMap0497 sourceMap0497_checked fusedMap0497_checked
    DegreeOneSmallComparisons.comparison0497
#print axioms sourceMap0497_checked
#print axioms fusedMap0497_checked
#print axioms certified0497
def sourceMap0497swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0497swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0497swap_checked : acceptsGraphIso
    (source (graph core0497) (root 7) 2 0) DegreeOneSmallSpectrum478.graph sourceMap0497swap=true := by decide +kernel
theorem fusedMap0497swap_checked : acceptsGraphIso
    (fused (graph core0497) (root 7) 2 0) DegreeOneSmallSpectrum372.graph fusedMap0497swap=true := by decide +kernel
theorem certified0497swap : Certified (graph core0497) (root 7) 2 0 :=
  of_native_maps core0497 DegreeOneSmallSpectrum478.graph DegreeOneSmallSpectrum372.graph
    sourceMap0497swap fusedMap0497swap sourceMap0497swap_checked fusedMap0497swap_checked
    DegreeOneSmallComparisons.comparison0497
#print axioms sourceMap0497swap_checked
#print axioms fusedMap0497swap_checked
#print axioms certified0497swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
