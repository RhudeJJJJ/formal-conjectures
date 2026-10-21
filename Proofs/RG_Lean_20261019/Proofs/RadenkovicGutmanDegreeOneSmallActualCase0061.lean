/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0061 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0061 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (sourceLabel 3 0 6 v)
def fusedMap0061 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 0 6 v)
theorem sourceMap0061_checked : acceptsGraphIso
    (source (graph core0061) (root 3) 0 6) DegreeOneSmallSpectrum392.graph sourceMap0061=true := by decide +kernel
theorem fusedMap0061_checked : acceptsGraphIso
    (fused (graph core0061) (root 3) 0 6) DegreeOneSmallSpectrum369.graph fusedMap0061=true := by decide +kernel
theorem certified0061 : Certified (graph core0061) (root 3) 0 6 :=
  of_native_maps core0061 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0061 fusedMap0061 sourceMap0061_checked fusedMap0061_checked
    DegreeOneSmallComparisons.comparison0061
#print axioms sourceMap0061_checked
#print axioms fusedMap0061_checked
#print axioms certified0061
def sourceMap0061swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,11,6] (sourceLabel 3 6 0 v)
def fusedMap0061swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10,11] (fusedLabel 3 6 0 v)
theorem sourceMap0061swap_checked : acceptsGraphIso
    (source (graph core0061) (root 3) 6 0) DegreeOneSmallSpectrum392.graph sourceMap0061swap=true := by decide +kernel
theorem fusedMap0061swap_checked : acceptsGraphIso
    (fused (graph core0061) (root 3) 6 0) DegreeOneSmallSpectrum369.graph fusedMap0061swap=true := by decide +kernel
theorem certified0061swap : Certified (graph core0061) (root 3) 6 0 :=
  of_native_maps core0061 DegreeOneSmallSpectrum392.graph DegreeOneSmallSpectrum369.graph
    sourceMap0061swap fusedMap0061swap sourceMap0061swap_checked fusedMap0061swap_checked
    DegreeOneSmallComparisons.comparison0061
#print axioms sourceMap0061swap_checked
#print axioms fusedMap0061swap_checked
#print axioms certified0061swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
