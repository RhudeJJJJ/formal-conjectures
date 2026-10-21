/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0015 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0015 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,5,3,4,1,0,6,7,8,9,10] (sourceLabel 1 1 6 v)
def fusedMap0015 : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 1 6 v)
theorem sourceMap0015_checked : acceptsGraphIso
    (source (graph core0015) (root 1) 1 6) DegreeOneSmallSpectrum165.graph sourceMap0015=true := by decide +kernel
theorem fusedMap0015_checked : acceptsGraphIso
    (fused (graph core0015) (root 1) 1 6) DegreeOneSmallSpectrum168.graph fusedMap0015=true := by decide +kernel
theorem certified0015 : Certified (graph core0015) (root 1) 1 6 :=
  of_native_maps core0015 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0015 fusedMap0015 sourceMap0015_checked fusedMap0015_checked
    DegreeOneSmallComparisons.comparison0015
#print axioms sourceMap0015_checked
#print axioms fusedMap0015_checked
#print axioms certified0015
def sourceMap0015swap : (Vertices 1 ⊕ Fin 7 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,5,1,0,6,7,8,9,10,3,4] (sourceLabel 1 6 1 v)
def fusedMap0015swap : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 6 1 v)
theorem sourceMap0015swap_checked : acceptsGraphIso
    (source (graph core0015) (root 1) 6 1) DegreeOneSmallSpectrum165.graph sourceMap0015swap=true := by decide +kernel
theorem fusedMap0015swap_checked : acceptsGraphIso
    (fused (graph core0015) (root 1) 6 1) DegreeOneSmallSpectrum168.graph fusedMap0015swap=true := by decide +kernel
theorem certified0015swap : Certified (graph core0015) (root 1) 6 1 :=
  of_native_maps core0015 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0015swap fusedMap0015swap sourceMap0015swap_checked fusedMap0015swap_checked
    DegreeOneSmallComparisons.comparison0015
#print axioms sourceMap0015swap_checked
#print axioms fusedMap0015swap_checked
#print axioms certified0015swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
