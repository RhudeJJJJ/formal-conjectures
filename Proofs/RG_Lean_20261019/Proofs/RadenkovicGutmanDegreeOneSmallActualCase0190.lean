/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0190 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0190 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0190 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0190_checked : acceptsGraphIso
    (source (graph core0190) (root 5) 1 2) DegreeOneSmallSpectrum214.graph sourceMap0190=true := by decide +kernel
theorem fusedMap0190_checked : acceptsGraphIso
    (fused (graph core0190) (root 5) 1 2) DegreeOneSmallSpectrum165.graph fusedMap0190=true := by decide +kernel
theorem certified0190 : Certified (graph core0190) (root 5) 1 2 :=
  of_native_maps core0190 DegreeOneSmallSpectrum214.graph DegreeOneSmallSpectrum165.graph
    sourceMap0190 fusedMap0190 sourceMap0190_checked fusedMap0190_checked
    DegreeOneSmallComparisons.comparison0190
#print axioms sourceMap0190_checked
#print axioms fusedMap0190_checked
#print axioms certified0190
def sourceMap0190swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0190swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0190swap_checked : acceptsGraphIso
    (source (graph core0190) (root 5) 2 1) DegreeOneSmallSpectrum214.graph sourceMap0190swap=true := by decide +kernel
theorem fusedMap0190swap_checked : acceptsGraphIso
    (fused (graph core0190) (root 5) 2 1) DegreeOneSmallSpectrum165.graph fusedMap0190swap=true := by decide +kernel
theorem certified0190swap : Certified (graph core0190) (root 5) 2 1 :=
  of_native_maps core0190 DegreeOneSmallSpectrum214.graph DegreeOneSmallSpectrum165.graph
    sourceMap0190swap fusedMap0190swap sourceMap0190swap_checked fusedMap0190swap_checked
    DegreeOneSmallComparisons.comparison0190
#print axioms sourceMap0190swap_checked
#print axioms fusedMap0190swap_checked
#print axioms certified0190swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
