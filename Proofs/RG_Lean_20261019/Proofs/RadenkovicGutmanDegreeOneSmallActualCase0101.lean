/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0101 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0101 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap0101 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap0101_checked : acceptsGraphIso
    (source (graph core0101) (root 4) 0 6) DegreeOneSmallSpectrum859.graph sourceMap0101=true := by decide +kernel
theorem fusedMap0101_checked : acceptsGraphIso
    (fused (graph core0101) (root 4) 0 6) DegreeOneSmallSpectrum861.graph fusedMap0101=true := by decide +kernel
theorem certified0101 : Certified (graph core0101) (root 4) 0 6 :=
  of_native_maps core0101 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0101 fusedMap0101 sourceMap0101_checked fusedMap0101_checked
    DegreeOneSmallComparisons.comparison0101
#print axioms sourceMap0101_checked
#print axioms fusedMap0101_checked
#print axioms certified0101
def sourceMap0101swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,11,12,6] (sourceLabel 4 6 0 v)
def fusedMap0101swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap0101swap_checked : acceptsGraphIso
    (source (graph core0101) (root 4) 6 0) DegreeOneSmallSpectrum859.graph sourceMap0101swap=true := by decide +kernel
theorem fusedMap0101swap_checked : acceptsGraphIso
    (fused (graph core0101) (root 4) 6 0) DegreeOneSmallSpectrum861.graph fusedMap0101swap=true := by decide +kernel
theorem certified0101swap : Certified (graph core0101) (root 4) 6 0 :=
  of_native_maps core0101 DegreeOneSmallSpectrum859.graph DegreeOneSmallSpectrum861.graph
    sourceMap0101swap fusedMap0101swap sourceMap0101swap_checked fusedMap0101swap_checked
    DegreeOneSmallComparisons.comparison0101
#print axioms sourceMap0101swap_checked
#print axioms fusedMap0101swap_checked
#print axioms certified0101swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
