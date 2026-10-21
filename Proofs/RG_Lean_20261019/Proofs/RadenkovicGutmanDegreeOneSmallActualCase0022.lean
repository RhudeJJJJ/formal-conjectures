/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0022 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0022 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,6,3,4,5,1,0,7,8,9,10,11] (sourceLabel 1 2 6 v)
def fusedMap0022 : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 2 6 v)
theorem sourceMap0022_checked : acceptsGraphIso
    (source (graph core0022) (root 1) 2 6) DegreeOneSmallSpectrum392.graph sourceMap0022=true := by decide +kernel
theorem fusedMap0022_checked : acceptsGraphIso
    (fused (graph core0022) (root 1) 2 6) DegreeOneSmallSpectrum369.graph fusedMap0022=true := by decide +kernel
theorem certified0022 : Certified (graph core0022) (root 1) 2 6 :=
  of_native_maps core0022 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0022 fusedMap0022 sourceMap0022_checked fusedMap0022_checked
    DegreeOneSmallComparisons.comparison0022
#print axioms sourceMap0022_checked
#print axioms fusedMap0022_checked
#print axioms certified0022
def sourceMap0022swap : (Vertices 1 ⊕ Fin 7 ⊕ Fin 3) → Fin 12 :=
  fun v => ![2,6,1,0,7,8,9,10,11,3,4,5] (sourceLabel 1 6 2 v)
def fusedMap0022swap : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 6 2 v)
theorem sourceMap0022swap_checked : acceptsGraphIso
    (source (graph core0022) (root 1) 6 2) DegreeOneSmallSpectrum392.graph sourceMap0022swap=true := by decide +kernel
theorem fusedMap0022swap_checked : acceptsGraphIso
    (fused (graph core0022) (root 1) 6 2) DegreeOneSmallSpectrum369.graph fusedMap0022swap=true := by decide +kernel
theorem certified0022swap : Certified (graph core0022) (root 1) 6 2 :=
  of_native_maps core0022 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0022swap fusedMap0022swap sourceMap0022swap_checked fusedMap0022swap_checked
    DegreeOneSmallComparisons.comparison0022
#print axioms sourceMap0022swap_checked
#print axioms fusedMap0022swap_checked
#print axioms certified0022swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
