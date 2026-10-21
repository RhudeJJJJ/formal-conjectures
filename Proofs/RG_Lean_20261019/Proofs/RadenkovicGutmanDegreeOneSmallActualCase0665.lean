/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0665 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0665 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0665 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0665_checked : acceptsGraphIso
    (source (graph core0665) (root 7) 0 2) SmallGeFourSpectrum109.graph sourceMap0665=true := by decide +kernel
theorem fusedMap0665_checked : acceptsGraphIso
    (fused (graph core0665) (root 7) 0 2) SmallGeFourSpectrum110.graph fusedMap0665=true := by decide +kernel
theorem certified0665 : Certified (graph core0665) (root 7) 0 2 :=
  of_native_maps core0665 SmallGeFourSpectrum109.graph SmallGeFourSpectrum110.graph
    sourceMap0665 fusedMap0665 sourceMap0665_checked fusedMap0665_checked
    DegreeOneSmallComparisons.comparison0665
#print axioms sourceMap0665_checked
#print axioms fusedMap0665_checked
#print axioms certified0665
def sourceMap0665swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0665swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0665swap_checked : acceptsGraphIso
    (source (graph core0665) (root 7) 2 0) SmallGeFourSpectrum109.graph sourceMap0665swap=true := by decide +kernel
theorem fusedMap0665swap_checked : acceptsGraphIso
    (fused (graph core0665) (root 7) 2 0) SmallGeFourSpectrum110.graph fusedMap0665swap=true := by decide +kernel
theorem certified0665swap : Certified (graph core0665) (root 7) 2 0 :=
  of_native_maps core0665 SmallGeFourSpectrum109.graph SmallGeFourSpectrum110.graph
    sourceMap0665swap fusedMap0665swap sourceMap0665swap_checked fusedMap0665swap_checked
    DegreeOneSmallComparisons.comparison0665
#print axioms sourceMap0665swap_checked
#print axioms fusedMap0665swap_checked
#print axioms certified0665swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
