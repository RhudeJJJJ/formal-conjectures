/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0888 : Family 8 := level8.get ⟨49,by decide⟩
def sourceMap0888 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap0888 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0888_checked : acceptsGraphIso
    (source (graph core0888) (root 8) 0 1) DegreeOneSmallSpectrum488.graph sourceMap0888=true := by decide +kernel
theorem fusedMap0888_checked : acceptsGraphIso
    (fused (graph core0888) (root 8) 0 1) DegreeOneSmallSpectrum499.graph fusedMap0888=true := by decide +kernel
theorem certified0888 : Certified (graph core0888) (root 8) 0 1 :=
  of_native_maps core0888 DegreeOneSmallSpectrum488.graph DegreeOneSmallSpectrum499.graph
    sourceMap0888 fusedMap0888 sourceMap0888_checked fusedMap0888_checked
    DegreeOneSmallComparisons.comparison0888
#print axioms sourceMap0888_checked
#print axioms fusedMap0888_checked
#print axioms certified0888
def sourceMap0888swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap0888swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0888swap_checked : acceptsGraphIso
    (source (graph core0888) (root 8) 1 0) DegreeOneSmallSpectrum488.graph sourceMap0888swap=true := by decide +kernel
theorem fusedMap0888swap_checked : acceptsGraphIso
    (fused (graph core0888) (root 8) 1 0) DegreeOneSmallSpectrum499.graph fusedMap0888swap=true := by decide +kernel
theorem certified0888swap : Certified (graph core0888) (root 8) 1 0 :=
  of_native_maps core0888 DegreeOneSmallSpectrum488.graph DegreeOneSmallSpectrum499.graph
    sourceMap0888swap fusedMap0888swap sourceMap0888swap_checked fusedMap0888swap_checked
    DegreeOneSmallComparisons.comparison0888
#print axioms sourceMap0888swap_checked
#print axioms fusedMap0888swap_checked
#print axioms certified0888swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
