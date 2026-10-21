/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0563 : Family 7 := level7.get ⟨26,by decide⟩
def sourceMap0563 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0563 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0563_checked : acceptsGraphIso
    (source (graph core0563) (root 7) 0 2) DegreeOneSmallSpectrum403.graph sourceMap0563=true := by decide +kernel
theorem fusedMap0563_checked : acceptsGraphIso
    (fused (graph core0563) (root 7) 0 2) SmallGeFourSpectrum094.graph fusedMap0563=true := by decide +kernel
theorem certified0563 : Certified (graph core0563) (root 7) 0 2 :=
  of_native_maps core0563 DegreeOneSmallSpectrum403.graph SmallGeFourSpectrum094.graph
    sourceMap0563 fusedMap0563 sourceMap0563_checked fusedMap0563_checked
    DegreeOneSmallComparisons.comparison0563
#print axioms sourceMap0563_checked
#print axioms fusedMap0563_checked
#print axioms certified0563
def sourceMap0563swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0563swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0563swap_checked : acceptsGraphIso
    (source (graph core0563) (root 7) 2 0) DegreeOneSmallSpectrum403.graph sourceMap0563swap=true := by decide +kernel
theorem fusedMap0563swap_checked : acceptsGraphIso
    (fused (graph core0563) (root 7) 2 0) SmallGeFourSpectrum094.graph fusedMap0563swap=true := by decide +kernel
theorem certified0563swap : Certified (graph core0563) (root 7) 2 0 :=
  of_native_maps core0563 DegreeOneSmallSpectrum403.graph SmallGeFourSpectrum094.graph
    sourceMap0563swap fusedMap0563swap sourceMap0563swap_checked fusedMap0563swap_checked
    DegreeOneSmallComparisons.comparison0563
#print axioms sourceMap0563swap_checked
#print axioms fusedMap0563swap_checked
#print axioms certified0563swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
