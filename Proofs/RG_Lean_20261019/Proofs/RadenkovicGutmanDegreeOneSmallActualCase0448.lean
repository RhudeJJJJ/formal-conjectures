/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0448 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0448 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 7 0 1 v)
def fusedMap0448 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (fusedLabel 7 0 1 v)
theorem sourceMap0448_checked : acceptsGraphIso
    (source (graph core0448) (root 7) 0 1) DegreeOneSmallSpectrum165.graph sourceMap0448=true := by decide +kernel
theorem fusedMap0448_checked : acceptsGraphIso
    (fused (graph core0448) (root 7) 0 1) DegreeOneSmallSpectrum168.graph fusedMap0448=true := by decide +kernel
theorem certified0448 : Certified (graph core0448) (root 7) 0 1 :=
  of_native_maps core0448 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0448 fusedMap0448 sourceMap0448_checked fusedMap0448_checked
    DegreeOneSmallComparisons.comparison0448
#print axioms sourceMap0448_checked
#print axioms fusedMap0448_checked
#print axioms certified0448
def sourceMap0448swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 7 1 0 v)
def fusedMap0448swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (fusedLabel 7 1 0 v)
theorem sourceMap0448swap_checked : acceptsGraphIso
    (source (graph core0448) (root 7) 1 0) DegreeOneSmallSpectrum165.graph sourceMap0448swap=true := by decide +kernel
theorem fusedMap0448swap_checked : acceptsGraphIso
    (fused (graph core0448) (root 7) 1 0) DegreeOneSmallSpectrum168.graph fusedMap0448swap=true := by decide +kernel
theorem certified0448swap : Certified (graph core0448) (root 7) 1 0 :=
  of_native_maps core0448 DegreeOneSmallSpectrum165.graph DegreeOneSmallSpectrum168.graph
    sourceMap0448swap fusedMap0448swap sourceMap0448swap_checked fusedMap0448swap_checked
    DegreeOneSmallComparisons.comparison0448
#print axioms sourceMap0448swap_checked
#print axioms fusedMap0448swap_checked
#print axioms certified0448swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
