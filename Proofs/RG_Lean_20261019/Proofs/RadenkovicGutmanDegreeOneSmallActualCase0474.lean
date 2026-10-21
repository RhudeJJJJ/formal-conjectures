/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0474 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0474 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 7 0 3 v)
def fusedMap0474 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0474_checked : acceptsGraphIso
    (source (graph core0474) (root 7) 0 3) DegreeOneSmallSpectrum975.graph sourceMap0474=true := by decide +kernel
theorem fusedMap0474_checked : acceptsGraphIso
    (fused (graph core0474) (root 7) 0 3) DegreeOneSmallSpectrum859.graph fusedMap0474=true := by decide +kernel
theorem certified0474 : Certified (graph core0474) (root 7) 0 3 :=
  of_native_maps core0474 DegreeOneSmallSpectrum975.graph DegreeOneSmallSpectrum859.graph
    sourceMap0474 fusedMap0474 sourceMap0474_checked fusedMap0474_checked
    DegreeOneSmallComparisons.comparison0474
#print axioms sourceMap0474_checked
#print axioms fusedMap0474_checked
#print axioms certified0474
def sourceMap0474swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 7 3 0 v)
def fusedMap0474swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0474swap_checked : acceptsGraphIso
    (source (graph core0474) (root 7) 3 0) DegreeOneSmallSpectrum975.graph sourceMap0474swap=true := by decide +kernel
theorem fusedMap0474swap_checked : acceptsGraphIso
    (fused (graph core0474) (root 7) 3 0) DegreeOneSmallSpectrum859.graph fusedMap0474swap=true := by decide +kernel
theorem certified0474swap : Certified (graph core0474) (root 7) 3 0 :=
  of_native_maps core0474 DegreeOneSmallSpectrum975.graph DegreeOneSmallSpectrum859.graph
    sourceMap0474swap fusedMap0474swap sourceMap0474swap_checked fusedMap0474swap_checked
    DegreeOneSmallComparisons.comparison0474
#print axioms sourceMap0474swap_checked
#print axioms fusedMap0474swap_checked
#print axioms certified0474swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
