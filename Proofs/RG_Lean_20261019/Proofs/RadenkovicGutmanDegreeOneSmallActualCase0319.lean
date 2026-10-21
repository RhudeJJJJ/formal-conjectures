/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0319 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0319 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0319 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0319_checked : acceptsGraphIso
    (source (graph core0319) (root 6) 1 3) DegreeOneSmallSpectrum1081.graph sourceMap0319=true := by decide +kernel
theorem fusedMap0319_checked : acceptsGraphIso
    (fused (graph core0319) (root 6) 1 3) DegreeOneSmallSpectrum870.graph fusedMap0319=true := by decide +kernel
theorem certified0319 : Certified (graph core0319) (root 6) 1 3 :=
  of_native_maps core0319 DegreeOneSmallSpectrum1081.graph DegreeOneSmallSpectrum870.graph
    sourceMap0319 fusedMap0319 sourceMap0319_checked fusedMap0319_checked
    DegreeOneSmallComparisons.comparison0319
#print axioms sourceMap0319_checked
#print axioms fusedMap0319_checked
#print axioms certified0319
def sourceMap0319swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0319swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0319swap_checked : acceptsGraphIso
    (source (graph core0319) (root 6) 3 1) DegreeOneSmallSpectrum1081.graph sourceMap0319swap=true := by decide +kernel
theorem fusedMap0319swap_checked : acceptsGraphIso
    (fused (graph core0319) (root 6) 3 1) DegreeOneSmallSpectrum870.graph fusedMap0319swap=true := by decide +kernel
theorem certified0319swap : Certified (graph core0319) (root 6) 3 1 :=
  of_native_maps core0319 DegreeOneSmallSpectrum1081.graph DegreeOneSmallSpectrum870.graph
    sourceMap0319swap fusedMap0319swap sourceMap0319swap_checked fusedMap0319swap_checked
    DegreeOneSmallComparisons.comparison0319
#print axioms sourceMap0319swap_checked
#print axioms fusedMap0319swap_checked
#print axioms certified0319swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
