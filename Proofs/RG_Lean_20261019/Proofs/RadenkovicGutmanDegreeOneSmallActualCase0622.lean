/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0622 : Family 7 := level7.get ⟨42,by decide⟩
def sourceMap0622 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0622 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0622_checked : acceptsGraphIso
    (source (graph core0622) (root 7) 0 1) SmallGeFourSpectrum064.graph sourceMap0622=true := by decide +kernel
theorem fusedMap0622_checked : acceptsGraphIso
    (fused (graph core0622) (root 7) 0 1) SmallGeFourSpectrum038.graph fusedMap0622=true := by decide +kernel
theorem certified0622 : Certified (graph core0622) (root 7) 0 1 :=
  of_native_maps core0622 SmallGeFourSpectrum064.graph SmallGeFourSpectrum038.graph
    sourceMap0622 fusedMap0622 sourceMap0622_checked fusedMap0622_checked
    DegreeOneSmallComparisons.comparison0622
#print axioms sourceMap0622_checked
#print axioms fusedMap0622_checked
#print axioms certified0622
def sourceMap0622swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0622swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0622swap_checked : acceptsGraphIso
    (source (graph core0622) (root 7) 1 0) SmallGeFourSpectrum064.graph sourceMap0622swap=true := by decide +kernel
theorem fusedMap0622swap_checked : acceptsGraphIso
    (fused (graph core0622) (root 7) 1 0) SmallGeFourSpectrum038.graph fusedMap0622swap=true := by decide +kernel
theorem certified0622swap : Certified (graph core0622) (root 7) 1 0 :=
  of_native_maps core0622 SmallGeFourSpectrum064.graph SmallGeFourSpectrum038.graph
    sourceMap0622swap fusedMap0622swap sourceMap0622swap_checked fusedMap0622swap_checked
    DegreeOneSmallComparisons.comparison0622
#print axioms sourceMap0622swap_checked
#print axioms fusedMap0622swap_checked
#print axioms certified0622swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
