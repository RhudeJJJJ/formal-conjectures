/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0036 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0036 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (sourceLabel 2 0 6 v)
def fusedMap0036 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 0 6 v)
theorem sourceMap0036_checked : acceptsGraphIso
    (source (graph core0036) (root 2) 0 6) DegreeOneSmallSpectrum165.graph sourceMap0036=true := by decide +kernel
theorem fusedMap0036_checked : acceptsGraphIso
    (fused (graph core0036) (root 2) 0 6) DegreeOneSmallSpectrum168.graph fusedMap0036=true := by decide +kernel
theorem certified0036 : Certified (graph core0036) (root 2) 0 6 :=
  of_native_maps core0036 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0036 fusedMap0036 sourceMap0036_checked fusedMap0036_checked
    DegreeOneSmallComparisons.comparison0036
#print axioms sourceMap0036_checked
#print axioms fusedMap0036_checked
#print axioms certified0036
def sourceMap0036swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,3,4,1,0,6,7,8,9,10,5] (sourceLabel 2 6 0 v)
def fusedMap0036swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 6 0 v)
theorem sourceMap0036swap_checked : acceptsGraphIso
    (source (graph core0036) (root 2) 6 0) DegreeOneSmallSpectrum165.graph sourceMap0036swap=true := by decide +kernel
theorem fusedMap0036swap_checked : acceptsGraphIso
    (fused (graph core0036) (root 2) 6 0) DegreeOneSmallSpectrum168.graph fusedMap0036swap=true := by decide +kernel
theorem certified0036swap : Certified (graph core0036) (root 2) 6 0 :=
  of_native_maps core0036 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0036swap fusedMap0036swap sourceMap0036swap_checked fusedMap0036swap_checked
    DegreeOneSmallComparisons.comparison0036
#print axioms sourceMap0036swap_checked
#print axioms fusedMap0036swap_checked
#print axioms certified0036swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
