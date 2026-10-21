/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0748 : Family 8 := level8.get ⟨3,by decide⟩
def sourceMap0748 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 8 0 1 v)
def fusedMap0748 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0748_checked : acceptsGraphIso
    (source (graph core0748) (root 8) 0 1) DegreeOneSmallSpectrum384.graph sourceMap0748=true := by decide +kernel
theorem fusedMap0748_checked : acceptsGraphIso
    (fused (graph core0748) (root 8) 0 1) DegreeOneSmallSpectrum392.graph fusedMap0748=true := by decide +kernel
theorem certified0748 : Certified (graph core0748) (root 8) 0 1 :=
  of_native_maps core0748 DegreeOneSmallSpectrum384.graph DegreeOneSmallSpectrum392.graph
    sourceMap0748 fusedMap0748 sourceMap0748_checked fusedMap0748_checked
    DegreeOneSmallComparisons.comparison0748
#print axioms sourceMap0748_checked
#print axioms fusedMap0748_checked
#print axioms certified0748
def sourceMap0748swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 8 1 0 v)
def fusedMap0748swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0748swap_checked : acceptsGraphIso
    (source (graph core0748) (root 8) 1 0) DegreeOneSmallSpectrum384.graph sourceMap0748swap=true := by decide +kernel
theorem fusedMap0748swap_checked : acceptsGraphIso
    (fused (graph core0748) (root 8) 1 0) DegreeOneSmallSpectrum392.graph fusedMap0748swap=true := by decide +kernel
theorem certified0748swap : Certified (graph core0748) (root 8) 1 0 :=
  of_native_maps core0748 DegreeOneSmallSpectrum384.graph DegreeOneSmallSpectrum392.graph
    sourceMap0748swap fusedMap0748swap sourceMap0748swap_checked fusedMap0748swap_checked
    DegreeOneSmallComparisons.comparison0748
#print axioms sourceMap0748swap_checked
#print axioms fusedMap0748swap_checked
#print axioms certified0748swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
