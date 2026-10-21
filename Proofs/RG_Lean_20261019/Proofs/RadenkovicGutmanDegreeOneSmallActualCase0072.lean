/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0072 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0072 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 3 2 5 v)
def fusedMap0072 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 2 5 v)
theorem sourceMap0072_checked : acceptsGraphIso
    (source (graph core0072) (root 3) 2 5) DegreeOneSmallSpectrum945.graph sourceMap0072=true := by decide +kernel
theorem fusedMap0072_checked : acceptsGraphIso
    (fused (graph core0072) (root 3) 2 5) DegreeOneSmallSpectrum861.graph fusedMap0072=true := by decide +kernel
theorem certified0072 : Certified (graph core0072) (root 3) 2 5 :=
  of_native_maps core0072 DegreeOneSmallSpectrum945.graph DegreeOneSmallSpectrum861.graph
    sourceMap0072 fusedMap0072 sourceMap0072_checked fusedMap0072_checked
    DegreeOneSmallComparisons.comparison0072
#print axioms sourceMap0072_checked
#print axioms fusedMap0072_checked
#print axioms certified0072
def sourceMap0072swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,2,3,4,0,8,9,10,11,12,5,6,7] (sourceLabel 3 5 2 v)
def fusedMap0072swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 5 2 v)
theorem sourceMap0072swap_checked : acceptsGraphIso
    (source (graph core0072) (root 3) 5 2) DegreeOneSmallSpectrum945.graph sourceMap0072swap=true := by decide +kernel
theorem fusedMap0072swap_checked : acceptsGraphIso
    (fused (graph core0072) (root 3) 5 2) DegreeOneSmallSpectrum861.graph fusedMap0072swap=true := by decide +kernel
theorem certified0072swap : Certified (graph core0072) (root 3) 5 2 :=
  of_native_maps core0072 DegreeOneSmallSpectrum945.graph DegreeOneSmallSpectrum861.graph
    sourceMap0072swap fusedMap0072swap sourceMap0072swap_checked fusedMap0072swap_checked
    DegreeOneSmallComparisons.comparison0072
#print axioms sourceMap0072swap_checked
#print axioms fusedMap0072swap_checked
#print axioms certified0072swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
