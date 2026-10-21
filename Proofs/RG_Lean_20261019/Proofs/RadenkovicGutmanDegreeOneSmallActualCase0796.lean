/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0796 : Family 8 := level8.get ⟨17,by decide⟩
def sourceMap0796 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0796 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0796_checked : acceptsGraphIso
    (source (graph core0796) (root 8) 0 1) DegreeOneSmallSpectrum551.graph sourceMap0796=true := by decide +kernel
theorem fusedMap0796_checked : acceptsGraphIso
    (fused (graph core0796) (root 8) 0 1) DegreeOneSmallSpectrum382.graph fusedMap0796=true := by decide +kernel
theorem certified0796 : Certified (graph core0796) (root 8) 0 1 :=
  of_native_maps core0796 DegreeOneSmallSpectrum551.graph DegreeOneSmallSpectrum382.graph
    sourceMap0796 fusedMap0796 sourceMap0796_checked fusedMap0796_checked
    DegreeOneSmallComparisons.comparison0796
#print axioms sourceMap0796_checked
#print axioms fusedMap0796_checked
#print axioms certified0796
def sourceMap0796swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0796swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0796swap_checked : acceptsGraphIso
    (source (graph core0796) (root 8) 1 0) DegreeOneSmallSpectrum551.graph sourceMap0796swap=true := by decide +kernel
theorem fusedMap0796swap_checked : acceptsGraphIso
    (fused (graph core0796) (root 8) 1 0) DegreeOneSmallSpectrum382.graph fusedMap0796swap=true := by decide +kernel
theorem certified0796swap : Certified (graph core0796) (root 8) 1 0 :=
  of_native_maps core0796 DegreeOneSmallSpectrum551.graph DegreeOneSmallSpectrum382.graph
    sourceMap0796swap fusedMap0796swap sourceMap0796swap_checked fusedMap0796swap_checked
    DegreeOneSmallComparisons.comparison0796
#print axioms sourceMap0796swap_checked
#print axioms fusedMap0796swap_checked
#print axioms certified0796swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
