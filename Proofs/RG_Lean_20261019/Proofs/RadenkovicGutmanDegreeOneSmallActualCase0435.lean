/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0435 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0435 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0435 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0435_checked : acceptsGraphIso
    (source (graph core0435) (root 6) 1 2) SmallGeFourSpectrum187.graph sourceMap0435=true := by decide +kernel
theorem fusedMap0435_checked : acceptsGraphIso
    (fused (graph core0435) (root 6) 1 2) SmallGeFourSpectrum104.graph fusedMap0435=true := by decide +kernel
theorem certified0435 : Certified (graph core0435) (root 6) 1 2 :=
  of_native_maps core0435 SmallGeFourSpectrum187.graph SmallGeFourSpectrum104.graph
    sourceMap0435 fusedMap0435 sourceMap0435_checked fusedMap0435_checked
    DegreeOneSmallComparisons.comparison0435
#print axioms sourceMap0435_checked
#print axioms fusedMap0435_checked
#print axioms certified0435
def sourceMap0435swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0435swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0435swap_checked : acceptsGraphIso
    (source (graph core0435) (root 6) 2 1) SmallGeFourSpectrum187.graph sourceMap0435swap=true := by decide +kernel
theorem fusedMap0435swap_checked : acceptsGraphIso
    (fused (graph core0435) (root 6) 2 1) SmallGeFourSpectrum104.graph fusedMap0435swap=true := by decide +kernel
theorem certified0435swap : Certified (graph core0435) (root 6) 2 1 :=
  of_native_maps core0435 SmallGeFourSpectrum187.graph SmallGeFourSpectrum104.graph
    sourceMap0435swap fusedMap0435swap sourceMap0435swap_checked fusedMap0435swap_checked
    DegreeOneSmallComparisons.comparison0435
#print axioms sourceMap0435swap_checked
#print axioms fusedMap0435swap_checked
#print axioms certified0435swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
