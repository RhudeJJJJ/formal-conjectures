/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0476 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0476 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 7 1 2 v)
def fusedMap0476 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0476_checked : acceptsGraphIso
    (source (graph core0476) (root 7) 1 2) DegreeOneSmallSpectrum950.graph sourceMap0476=true := by decide +kernel
theorem fusedMap0476_checked : acceptsGraphIso
    (fused (graph core0476) (root 7) 1 2) DegreeOneSmallSpectrum859.graph fusedMap0476=true := by decide +kernel
theorem certified0476 : Certified (graph core0476) (root 7) 1 2 :=
  of_native_maps core0476 DegreeOneSmallSpectrum950.graph DegreeOneSmallSpectrum859.graph
    sourceMap0476 fusedMap0476 sourceMap0476_checked fusedMap0476_checked
    DegreeOneSmallComparisons.comparison0476
#print axioms sourceMap0476_checked
#print axioms fusedMap0476_checked
#print axioms certified0476
def sourceMap0476swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 2 1 v)
def fusedMap0476swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0476swap_checked : acceptsGraphIso
    (source (graph core0476) (root 7) 2 1) DegreeOneSmallSpectrum950.graph sourceMap0476swap=true := by decide +kernel
theorem fusedMap0476swap_checked : acceptsGraphIso
    (fused (graph core0476) (root 7) 2 1) DegreeOneSmallSpectrum859.graph fusedMap0476swap=true := by decide +kernel
theorem certified0476swap : Certified (graph core0476) (root 7) 2 1 :=
  of_native_maps core0476 DegreeOneSmallSpectrum950.graph DegreeOneSmallSpectrum859.graph
    sourceMap0476swap fusedMap0476swap sourceMap0476swap_checked fusedMap0476swap_checked
    DegreeOneSmallComparisons.comparison0476
#print axioms sourceMap0476swap_checked
#print axioms fusedMap0476swap_checked
#print axioms certified0476swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
