/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0980 : Family 8 := level8.get ⟨87,by decide⟩
def sourceMap0980 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0980 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0980_checked : acceptsGraphIso
    (source (graph core0980) (root 8) 0 1) SmallGeFourSpectrum105.graph sourceMap0980=true := by decide +kernel
theorem fusedMap0980_checked : acceptsGraphIso
    (fused (graph core0980) (root 8) 0 1) SmallGeFourSpectrum111.graph fusedMap0980=true := by decide +kernel
theorem certified0980 : Certified (graph core0980) (root 8) 0 1 :=
  of_native_maps core0980 SmallGeFourSpectrum105.graph SmallGeFourSpectrum111.graph
    sourceMap0980 fusedMap0980 sourceMap0980_checked fusedMap0980_checked
    DegreeOneSmallComparisons.comparison0980
#print axioms sourceMap0980_checked
#print axioms fusedMap0980_checked
#print axioms certified0980
def sourceMap0980swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0980swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0980swap_checked : acceptsGraphIso
    (source (graph core0980) (root 8) 1 0) SmallGeFourSpectrum105.graph sourceMap0980swap=true := by decide +kernel
theorem fusedMap0980swap_checked : acceptsGraphIso
    (fused (graph core0980) (root 8) 1 0) SmallGeFourSpectrum111.graph fusedMap0980swap=true := by decide +kernel
theorem certified0980swap : Certified (graph core0980) (root 8) 1 0 :=
  of_native_maps core0980 SmallGeFourSpectrum105.graph SmallGeFourSpectrum111.graph
    sourceMap0980swap fusedMap0980swap sourceMap0980swap_checked fusedMap0980swap_checked
    DegreeOneSmallComparisons.comparison0980
#print axioms sourceMap0980swap_checked
#print axioms fusedMap0980swap_checked
#print axioms certified0980swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
