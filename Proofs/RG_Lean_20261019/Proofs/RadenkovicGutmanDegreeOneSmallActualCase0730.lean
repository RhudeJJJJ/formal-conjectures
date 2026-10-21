/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0730 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0730 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0730 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0730_checked : acceptsGraphIso
    (source (graph core0730) (root 7) 0 1) SmallGeFourSpectrum074.graph sourceMap0730=true := by decide +kernel
theorem fusedMap0730_checked : acceptsGraphIso
    (fused (graph core0730) (root 7) 0 1) SmallGeFourSpectrum040.graph fusedMap0730=true := by decide +kernel
theorem certified0730 : Certified (graph core0730) (root 7) 0 1 :=
  of_native_maps core0730 SmallGeFourSpectrum074.graph SmallGeFourSpectrum040.graph
    sourceMap0730 fusedMap0730 sourceMap0730_checked fusedMap0730_checked
    DegreeOneSmallComparisons.comparison0730
#print axioms sourceMap0730_checked
#print axioms fusedMap0730_checked
#print axioms certified0730
def sourceMap0730swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0730swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0730swap_checked : acceptsGraphIso
    (source (graph core0730) (root 7) 1 0) SmallGeFourSpectrum074.graph sourceMap0730swap=true := by decide +kernel
theorem fusedMap0730swap_checked : acceptsGraphIso
    (fused (graph core0730) (root 7) 1 0) SmallGeFourSpectrum040.graph fusedMap0730swap=true := by decide +kernel
theorem certified0730swap : Certified (graph core0730) (root 7) 1 0 :=
  of_native_maps core0730 SmallGeFourSpectrum074.graph SmallGeFourSpectrum040.graph
    sourceMap0730swap fusedMap0730swap sourceMap0730swap_checked fusedMap0730swap_checked
    DegreeOneSmallComparisons.comparison0730
#print axioms sourceMap0730swap_checked
#print axioms fusedMap0730swap_checked
#print axioms certified0730swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
