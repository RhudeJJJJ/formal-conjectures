/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0452 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0452 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 7 1 2 v)
def fusedMap0452 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 7 1 2 v)
theorem sourceMap0452_checked : acceptsGraphIso
    (source (graph core0452) (root 7) 1 2) DegreeOneSmallSpectrum951.graph sourceMap0452=true := by decide +kernel
theorem fusedMap0452_checked : acceptsGraphIso
    (fused (graph core0452) (root 7) 1 2) DegreeOneSmallSpectrum861.graph fusedMap0452=true := by decide +kernel
theorem certified0452 : Certified (graph core0452) (root 7) 1 2 :=
  of_native_maps core0452 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0452 fusedMap0452 sourceMap0452_checked fusedMap0452_checked
    DegreeOneSmallComparisons.comparison0452
#print axioms sourceMap0452_checked
#print axioms fusedMap0452_checked
#print axioms certified0452
def sourceMap0452swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,3,4,5,6,7] (sourceLabel 7 2 1 v)
def fusedMap0452swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 7 2 1 v)
theorem sourceMap0452swap_checked : acceptsGraphIso
    (source (graph core0452) (root 7) 2 1) DegreeOneSmallSpectrum951.graph sourceMap0452swap=true := by decide +kernel
theorem fusedMap0452swap_checked : acceptsGraphIso
    (fused (graph core0452) (root 7) 2 1) DegreeOneSmallSpectrum861.graph fusedMap0452swap=true := by decide +kernel
theorem certified0452swap : Certified (graph core0452) (root 7) 2 1 :=
  of_native_maps core0452 DegreeOneSmallSpectrum951.graph DegreeOneSmallSpectrum861.graph
    sourceMap0452swap fusedMap0452swap sourceMap0452swap_checked fusedMap0452swap_checked
    DegreeOneSmallComparisons.comparison0452
#print axioms sourceMap0452swap_checked
#print axioms fusedMap0452swap_checked
#print axioms certified0452swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
