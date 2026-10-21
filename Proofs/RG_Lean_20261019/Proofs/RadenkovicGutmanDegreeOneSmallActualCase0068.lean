/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0068 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0068 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 3 1 6 v)
def fusedMap0068 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 1 6 v)
theorem sourceMap0068_checked : acceptsGraphIso
    (source (graph core0068) (root 3) 1 6) DegreeOneSmallSpectrum951.graph sourceMap0068=true := by decide +kernel
theorem fusedMap0068_checked : acceptsGraphIso
    (fused (graph core0068) (root 3) 1 6) DegreeOneSmallSpectrum861.graph fusedMap0068=true := by decide +kernel
theorem certified0068 : Certified (graph core0068) (root 3) 1 6 :=
  of_native_maps core0068 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0068 fusedMap0068 sourceMap0068_checked fusedMap0068_checked
    DegreeOneSmallComparisons.comparison0068
#print axioms sourceMap0068_checked
#print axioms fusedMap0068_checked
#print axioms certified0068
def sourceMap0068swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,5,1,0,8,9,10,11,12,6,7] (sourceLabel 3 6 1 v)
def fusedMap0068swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 6 1 v)
theorem sourceMap0068swap_checked : acceptsGraphIso
    (source (graph core0068) (root 3) 6 1) DegreeOneSmallSpectrum951.graph sourceMap0068swap=true := by decide +kernel
theorem fusedMap0068swap_checked : acceptsGraphIso
    (fused (graph core0068) (root 3) 6 1) DegreeOneSmallSpectrum861.graph fusedMap0068swap=true := by decide +kernel
theorem certified0068swap : Certified (graph core0068) (root 3) 6 1 :=
  of_native_maps core0068 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0068swap fusedMap0068swap sourceMap0068swap_checked fusedMap0068swap_checked
    DegreeOneSmallComparisons.comparison0068
#print axioms sourceMap0068swap_checked
#print axioms fusedMap0068swap_checked
#print axioms certified0068swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
