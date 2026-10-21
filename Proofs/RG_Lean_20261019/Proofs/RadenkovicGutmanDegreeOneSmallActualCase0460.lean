/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0460 : Family 7 := level7.get ⟨2,by decide⟩
def sourceMap0460 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 7 0 1 v)
def fusedMap0460 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0460_checked : acceptsGraphIso
    (source (graph core0460) (root 7) 0 1) DegreeOneSmallSpectrum213.graph sourceMap0460=true := by decide +kernel
theorem fusedMap0460_checked : acceptsGraphIso
    (fused (graph core0460) (root 7) 0 1) DegreeOneSmallSpectrum165.graph fusedMap0460=true := by decide +kernel
theorem certified0460 : Certified (graph core0460) (root 7) 0 1 :=
  of_native_maps core0460 DegreeOneSmallSpectrum213.graph DegreeOneSmallSpectrum165.graph
    sourceMap0460 fusedMap0460 sourceMap0460_checked fusedMap0460_checked
    DegreeOneSmallComparisons.comparison0460
#print axioms sourceMap0460_checked
#print axioms fusedMap0460_checked
#print axioms certified0460
def sourceMap0460swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 7 1 0 v)
def fusedMap0460swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0460swap_checked : acceptsGraphIso
    (source (graph core0460) (root 7) 1 0) DegreeOneSmallSpectrum213.graph sourceMap0460swap=true := by decide +kernel
theorem fusedMap0460swap_checked : acceptsGraphIso
    (fused (graph core0460) (root 7) 1 0) DegreeOneSmallSpectrum165.graph fusedMap0460swap=true := by decide +kernel
theorem certified0460swap : Certified (graph core0460) (root 7) 1 0 :=
  of_native_maps core0460 DegreeOneSmallSpectrum213.graph DegreeOneSmallSpectrum165.graph
    sourceMap0460swap fusedMap0460swap sourceMap0460swap_checked fusedMap0460swap_checked
    DegreeOneSmallComparisons.comparison0460
#print axioms sourceMap0460swap_checked
#print axioms fusedMap0460swap_checked
#print axioms certified0460swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
