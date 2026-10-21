/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0849 : Family 8 := level8.get ⟨36,by decide⟩
def sourceMap0849 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0849 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0849_checked : acceptsGraphIso
    (source (graph core0849) (root 8) 0 2) DegreeOneSmallSpectrum1058.graph sourceMap0849=true := by decide +kernel
theorem fusedMap0849_checked : acceptsGraphIso
    (fused (graph core0849) (root 8) 0 2) DegreeOneSmallSpectrum864.graph fusedMap0849=true := by decide +kernel
theorem certified0849 : Certified (graph core0849) (root 8) 0 2 :=
  of_native_maps core0849 DegreeOneSmallSpectrum1058.graph DegreeOneSmallSpectrum864.graph
    sourceMap0849 fusedMap0849 sourceMap0849_checked fusedMap0849_checked
    DegreeOneSmallComparisons.comparison0849
#print axioms sourceMap0849_checked
#print axioms fusedMap0849_checked
#print axioms certified0849
def sourceMap0849swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0849swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0849swap_checked : acceptsGraphIso
    (source (graph core0849) (root 8) 2 0) DegreeOneSmallSpectrum1058.graph sourceMap0849swap=true := by decide +kernel
theorem fusedMap0849swap_checked : acceptsGraphIso
    (fused (graph core0849) (root 8) 2 0) DegreeOneSmallSpectrum864.graph fusedMap0849swap=true := by decide +kernel
theorem certified0849swap : Certified (graph core0849) (root 8) 2 0 :=
  of_native_maps core0849 DegreeOneSmallSpectrum1058.graph DegreeOneSmallSpectrum864.graph
    sourceMap0849swap fusedMap0849swap sourceMap0849swap_checked fusedMap0849swap_checked
    DegreeOneSmallComparisons.comparison0849
#print axioms sourceMap0849swap_checked
#print axioms fusedMap0849swap_checked
#print axioms certified0849swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
