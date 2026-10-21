/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0021 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0021 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,5,2,3,4,0,6,7,8,9,10] (sourceLabel 1 2 5 v)
def fusedMap0021 : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 2 5 v)
theorem sourceMap0021_checked : acceptsGraphIso
    (source (graph core0021) (root 1) 2 5) DegreeOneSmallSpectrum166.graph sourceMap0021=true := by decide +kernel
theorem fusedMap0021_checked : acceptsGraphIso
    (fused (graph core0021) (root 1) 2 5) DegreeOneSmallSpectrum168.graph fusedMap0021=true := by decide +kernel
theorem certified0021 : Certified (graph core0021) (root 1) 2 5 :=
  of_native_maps core0021 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0021 fusedMap0021 sourceMap0021_checked fusedMap0021_checked
    DegreeOneSmallComparisons.comparison0021
#print axioms sourceMap0021_checked
#print axioms fusedMap0021_checked
#print axioms certified0021
def sourceMap0021swap : (Vertices 1 ⊕ Fin 6 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,5,0,6,7,8,9,10,2,3,4] (sourceLabel 1 5 2 v)
def fusedMap0021swap : (Vertices 1 ⊕ Fin 9) → Fin 11 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10] (fusedLabel 1 5 2 v)
theorem sourceMap0021swap_checked : acceptsGraphIso
    (source (graph core0021) (root 1) 5 2) DegreeOneSmallSpectrum166.graph sourceMap0021swap=true := by decide +kernel
theorem fusedMap0021swap_checked : acceptsGraphIso
    (fused (graph core0021) (root 1) 5 2) DegreeOneSmallSpectrum168.graph fusedMap0021swap=true := by decide +kernel
theorem certified0021swap : Certified (graph core0021) (root 1) 5 2 :=
  of_native_maps core0021 DegreeOneSmallSpectrum166.graph DegreeOneSmallSpectrum168.graph
    sourceMap0021swap fusedMap0021swap sourceMap0021swap_checked fusedMap0021swap_checked
    DegreeOneSmallComparisons.comparison0021
#print axioms sourceMap0021swap_checked
#print axioms fusedMap0021swap_checked
#print axioms certified0021swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
