/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0370 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0370 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0370 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0370_checked : acceptsGraphIso
    (source (graph core0370) (root 6) 0 4) DegreeOneSmallSpectrum948.graph sourceMap0370=true := by decide +kernel
theorem fusedMap0370_checked : acceptsGraphIso
    (fused (graph core0370) (root 6) 0 4) DegreeOneSmallSpectrum951.graph fusedMap0370=true := by decide +kernel
theorem certified0370 : Certified (graph core0370) (root 6) 0 4 :=
  of_native_maps core0370 DegreeOneSmallSpectrum948.graph DegreeOneSmallSpectrum951.graph
    sourceMap0370 fusedMap0370 sourceMap0370_checked fusedMap0370_checked
    DegreeOneSmallComparisons.comparison0370
#print axioms sourceMap0370_checked
#print axioms fusedMap0370_checked
#print axioms certified0370
def sourceMap0370swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0370swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0370swap_checked : acceptsGraphIso
    (source (graph core0370) (root 6) 4 0) DegreeOneSmallSpectrum948.graph sourceMap0370swap=true := by decide +kernel
theorem fusedMap0370swap_checked : acceptsGraphIso
    (fused (graph core0370) (root 6) 4 0) DegreeOneSmallSpectrum951.graph fusedMap0370swap=true := by decide +kernel
theorem certified0370swap : Certified (graph core0370) (root 6) 4 0 :=
  of_native_maps core0370 DegreeOneSmallSpectrum948.graph DegreeOneSmallSpectrum951.graph
    sourceMap0370swap fusedMap0370swap sourceMap0370swap_checked fusedMap0370swap_checked
    DegreeOneSmallComparisons.comparison0370
#print axioms sourceMap0370swap_checked
#print axioms fusedMap0370swap_checked
#print axioms certified0370swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
