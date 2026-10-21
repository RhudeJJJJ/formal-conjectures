/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0952 : Family 8 := level8.get ⟨75,by decide⟩
def sourceMap0952 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0952 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0952_checked : acceptsGraphIso
    (source (graph core0952) (root 8) 0 1) SmallGeFourSpectrum106.graph sourceMap0952=true := by decide +kernel
theorem fusedMap0952_checked : acceptsGraphIso
    (fused (graph core0952) (root 8) 0 1) SmallGeFourSpectrum110.graph fusedMap0952=true := by decide +kernel
theorem certified0952 : Certified (graph core0952) (root 8) 0 1 :=
  of_native_maps core0952 SmallGeFourSpectrum106.graph SmallGeFourSpectrum110.graph
    sourceMap0952 fusedMap0952 sourceMap0952_checked fusedMap0952_checked
    DegreeOneSmallComparisons.comparison0952
#print axioms sourceMap0952_checked
#print axioms fusedMap0952_checked
#print axioms certified0952
def sourceMap0952swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0952swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0952swap_checked : acceptsGraphIso
    (source (graph core0952) (root 8) 1 0) SmallGeFourSpectrum106.graph sourceMap0952swap=true := by decide +kernel
theorem fusedMap0952swap_checked : acceptsGraphIso
    (fused (graph core0952) (root 8) 1 0) SmallGeFourSpectrum110.graph fusedMap0952swap=true := by decide +kernel
theorem certified0952swap : Certified (graph core0952) (root 8) 1 0 :=
  of_native_maps core0952 SmallGeFourSpectrum106.graph SmallGeFourSpectrum110.graph
    sourceMap0952swap fusedMap0952swap sourceMap0952swap_checked fusedMap0952swap_checked
    DegreeOneSmallComparisons.comparison0952
#print axioms sourceMap0952swap_checked
#print axioms fusedMap0952swap_checked
#print axioms certified0952swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
