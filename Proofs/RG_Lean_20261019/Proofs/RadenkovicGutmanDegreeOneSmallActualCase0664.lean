/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0664 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0664 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0664 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0664_checked : acceptsGraphIso
    (source (graph core0664) (root 7) 0 1) SmallGeFourSpectrum066.graph sourceMap0664=true := by decide +kernel
theorem fusedMap0664_checked : acceptsGraphIso
    (fused (graph core0664) (root 7) 0 1) SmallGeFourSpectrum039.graph fusedMap0664=true := by decide +kernel
theorem certified0664 : Certified (graph core0664) (root 7) 0 1 :=
  of_native_maps core0664 SmallGeFourSpectrum066.graph SmallGeFourSpectrum039.graph
    sourceMap0664 fusedMap0664 sourceMap0664_checked fusedMap0664_checked
    DegreeOneSmallComparisons.comparison0664
#print axioms sourceMap0664_checked
#print axioms fusedMap0664_checked
#print axioms certified0664
def sourceMap0664swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0664swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0664swap_checked : acceptsGraphIso
    (source (graph core0664) (root 7) 1 0) SmallGeFourSpectrum066.graph sourceMap0664swap=true := by decide +kernel
theorem fusedMap0664swap_checked : acceptsGraphIso
    (fused (graph core0664) (root 7) 1 0) SmallGeFourSpectrum039.graph fusedMap0664swap=true := by decide +kernel
theorem certified0664swap : Certified (graph core0664) (root 7) 1 0 :=
  of_native_maps core0664 SmallGeFourSpectrum066.graph SmallGeFourSpectrum039.graph
    sourceMap0664swap fusedMap0664swap sourceMap0664swap_checked fusedMap0664swap_checked
    DegreeOneSmallComparisons.comparison0664
#print axioms sourceMap0664swap_checked
#print axioms fusedMap0664swap_checked
#print axioms certified0664swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
