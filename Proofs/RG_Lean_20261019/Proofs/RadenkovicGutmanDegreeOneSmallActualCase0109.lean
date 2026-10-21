/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0109 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0109 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap0109 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap0109_checked : acceptsGraphIso
    (source (graph core0109) (root 4) 2 4) DegreeOneSmallSpectrum967.graph sourceMap0109=true := by decide +kernel
theorem fusedMap0109_checked : acceptsGraphIso
    (fused (graph core0109) (root 4) 2 4) DegreeOneSmallSpectrum861.graph fusedMap0109=true := by decide +kernel
theorem certified0109 : Certified (graph core0109) (root 4) 2 4 :=
  of_native_maps core0109 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0109 fusedMap0109 sourceMap0109_checked fusedMap0109_checked
    DegreeOneSmallComparisons.comparison0109
#print axioms sourceMap0109_checked
#print axioms fusedMap0109_checked
#print axioms certified0109
def sourceMap0109swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,5,6,7] (sourceLabel 4 4 2 v)
def fusedMap0109swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap0109swap_checked : acceptsGraphIso
    (source (graph core0109) (root 4) 4 2) DegreeOneSmallSpectrum967.graph sourceMap0109swap=true := by decide +kernel
theorem fusedMap0109swap_checked : acceptsGraphIso
    (fused (graph core0109) (root 4) 4 2) DegreeOneSmallSpectrum861.graph fusedMap0109swap=true := by decide +kernel
theorem certified0109swap : Certified (graph core0109) (root 4) 4 2 :=
  of_native_maps core0109 DegreeOneSmallSpectrum967.graph DegreeOneSmallSpectrum861.graph
    sourceMap0109swap fusedMap0109swap sourceMap0109swap_checked fusedMap0109swap_checked
    DegreeOneSmallComparisons.comparison0109
#print axioms sourceMap0109swap_checked
#print axioms fusedMap0109swap_checked
#print axioms certified0109swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
