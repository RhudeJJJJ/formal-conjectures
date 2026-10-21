/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0479 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0479 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,5,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap0479 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 0 2 v)
theorem sourceMap0479_checked : acceptsGraphIso
    (source (graph core0479) (root 7) 0 2) DegreeOneSmallSpectrum389.graph sourceMap0479=true := by decide +kernel
theorem fusedMap0479_checked : acceptsGraphIso
    (fused (graph core0479) (root 7) 0 2) DegreeOneSmallSpectrum397.graph fusedMap0479=true := by decide +kernel
theorem certified0479 : Certified (graph core0479) (root 7) 0 2 :=
  of_native_maps core0479 DegreeOneSmallSpectrum389.graph DegreeOneSmallSpectrum397.graph
    sourceMap0479 fusedMap0479 sourceMap0479_checked fusedMap0479_checked
    DegreeOneSmallComparisons.comparison0479
#print axioms sourceMap0479_checked
#print axioms fusedMap0479_checked
#print axioms certified0479
def sourceMap0479swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 7 2 0 v)
def fusedMap0479swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 2 0 v)
theorem sourceMap0479swap_checked : acceptsGraphIso
    (source (graph core0479) (root 7) 2 0) DegreeOneSmallSpectrum389.graph sourceMap0479swap=true := by decide +kernel
theorem fusedMap0479swap_checked : acceptsGraphIso
    (fused (graph core0479) (root 7) 2 0) DegreeOneSmallSpectrum397.graph fusedMap0479swap=true := by decide +kernel
theorem certified0479swap : Certified (graph core0479) (root 7) 2 0 :=
  of_native_maps core0479 DegreeOneSmallSpectrum389.graph DegreeOneSmallSpectrum397.graph
    sourceMap0479swap fusedMap0479swap sourceMap0479swap_checked fusedMap0479swap_checked
    DegreeOneSmallComparisons.comparison0479
#print axioms sourceMap0479swap_checked
#print axioms fusedMap0479swap_checked
#print axioms certified0479swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
