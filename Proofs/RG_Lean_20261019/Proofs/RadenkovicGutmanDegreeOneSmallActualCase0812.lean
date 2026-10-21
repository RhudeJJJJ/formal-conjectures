/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0812 : Family 8 := level8.get ⟨22,by decide⟩
def sourceMap0812 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0812 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0812_checked : acceptsGraphIso
    (source (graph core0812) (root 8) 0 1) DegreeOneSmallSpectrum558.graph sourceMap0812=true := by decide +kernel
theorem fusedMap0812_checked : acceptsGraphIso
    (fused (graph core0812) (root 8) 0 1) DegreeOneSmallSpectrum389.graph fusedMap0812=true := by decide +kernel
theorem certified0812 : Certified (graph core0812) (root 8) 0 1 :=
  of_native_maps core0812 DegreeOneSmallSpectrum558.graph DegreeOneSmallSpectrum389.graph
    sourceMap0812 fusedMap0812 sourceMap0812_checked fusedMap0812_checked
    DegreeOneSmallComparisons.comparison0812
#print axioms sourceMap0812_checked
#print axioms fusedMap0812_checked
#print axioms certified0812
def sourceMap0812swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0812swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0812swap_checked : acceptsGraphIso
    (source (graph core0812) (root 8) 1 0) DegreeOneSmallSpectrum558.graph sourceMap0812swap=true := by decide +kernel
theorem fusedMap0812swap_checked : acceptsGraphIso
    (fused (graph core0812) (root 8) 1 0) DegreeOneSmallSpectrum389.graph fusedMap0812swap=true := by decide +kernel
theorem certified0812swap : Certified (graph core0812) (root 8) 1 0 :=
  of_native_maps core0812 DegreeOneSmallSpectrum558.graph DegreeOneSmallSpectrum389.graph
    sourceMap0812swap fusedMap0812swap sourceMap0812swap_checked fusedMap0812swap_checked
    DegreeOneSmallComparisons.comparison0812
#print axioms sourceMap0812swap_checked
#print axioms fusedMap0812swap_checked
#print axioms certified0812swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
