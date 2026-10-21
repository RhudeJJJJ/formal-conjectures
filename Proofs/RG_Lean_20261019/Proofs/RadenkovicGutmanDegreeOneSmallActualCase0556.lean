/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0556 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0556 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,4,2,3] (sourceLabel 7 0 1 v)
def fusedMap0556 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (fusedLabel 7 0 1 v)
theorem sourceMap0556_checked : acceptsGraphIso
    (source (graph core0556) (root 7) 0 1) DegreeOneSmallSpectrum209.graph sourceMap0556=true := by decide +kernel
theorem fusedMap0556_checked : acceptsGraphIso
    (fused (graph core0556) (root 7) 0 1) DegreeOneSmallSpectrum229.graph fusedMap0556=true := by decide +kernel
theorem certified0556 : Certified (graph core0556) (root 7) 0 1 :=
  of_native_maps core0556 DegreeOneSmallSpectrum209.graph DegreeOneSmallSpectrum229.graph
    sourceMap0556 fusedMap0556 sourceMap0556_checked fusedMap0556_checked
    DegreeOneSmallComparisons.comparison0556
#print axioms sourceMap0556_checked
#print axioms fusedMap0556_checked
#print axioms certified0556
def sourceMap0556swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 7 1 0 v)
def fusedMap0556swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (fusedLabel 7 1 0 v)
theorem sourceMap0556swap_checked : acceptsGraphIso
    (source (graph core0556) (root 7) 1 0) DegreeOneSmallSpectrum209.graph sourceMap0556swap=true := by decide +kernel
theorem fusedMap0556swap_checked : acceptsGraphIso
    (fused (graph core0556) (root 7) 1 0) DegreeOneSmallSpectrum229.graph fusedMap0556swap=true := by decide +kernel
theorem certified0556swap : Certified (graph core0556) (root 7) 1 0 :=
  of_native_maps core0556 DegreeOneSmallSpectrum209.graph DegreeOneSmallSpectrum229.graph
    sourceMap0556swap fusedMap0556swap sourceMap0556swap_checked fusedMap0556swap_checked
    DegreeOneSmallComparisons.comparison0556
#print axioms sourceMap0556swap_checked
#print axioms fusedMap0556swap_checked
#print axioms certified0556swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
