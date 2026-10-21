/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0060 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0060 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (sourceLabel 3 0 5 v)
def fusedMap0060 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 0 5 v)
theorem sourceMap0060_checked : acceptsGraphIso
    (source (graph core0060) (root 3) 0 5) DegreeOneSmallSpectrum166.graph sourceMap0060=true := by decide +kernel
theorem fusedMap0060_checked : acceptsGraphIso
    (fused (graph core0060) (root 3) 0 5) DegreeOneSmallSpectrum168.graph fusedMap0060=true := by decide +kernel
theorem certified0060 : Certified (graph core0060) (root 3) 0 5 :=
  of_native_maps core0060 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0060 fusedMap0060 sourceMap0060_checked fusedMap0060_checked
    DegreeOneSmallComparisons.comparison0060
#print axioms sourceMap0060_checked
#print axioms fusedMap0060_checked
#print axioms certified0060
def sourceMap0060swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,0,6,7,8,9,10,5] (sourceLabel 3 5 0 v)
def fusedMap0060swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 5 0 v)
theorem sourceMap0060swap_checked : acceptsGraphIso
    (source (graph core0060) (root 3) 5 0) DegreeOneSmallSpectrum166.graph sourceMap0060swap=true := by decide +kernel
theorem fusedMap0060swap_checked : acceptsGraphIso
    (fused (graph core0060) (root 3) 5 0) DegreeOneSmallSpectrum168.graph fusedMap0060swap=true := by decide +kernel
theorem certified0060swap : Certified (graph core0060) (root 3) 5 0 :=
  of_native_maps core0060 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0060swap fusedMap0060swap sourceMap0060swap_checked fusedMap0060swap_checked
    DegreeOneSmallComparisons.comparison0060
#print axioms sourceMap0060swap_checked
#print axioms fusedMap0060swap_checked
#print axioms certified0060swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
