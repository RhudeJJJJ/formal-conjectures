/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0300 : Family 6 := level6.get ⟨3,by decide⟩
def sourceMap0300 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 6 1 2 v)
def fusedMap0300 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0300_checked : acceptsGraphIso
    (source (graph core0300) (root 6) 1 2) DegreeOneSmallSpectrum574.graph sourceMap0300=true := by decide +kernel
theorem fusedMap0300_checked : acceptsGraphIso
    (fused (graph core0300) (root 6) 1 2) DegreeOneSmallSpectrum392.graph fusedMap0300=true := by decide +kernel
theorem certified0300 : Certified (graph core0300) (root 6) 1 2 :=
  of_native_maps core0300 DegreeOneSmallSpectrum574.graph DegreeOneSmallSpectrum392.graph
    sourceMap0300 fusedMap0300 sourceMap0300_checked fusedMap0300_checked
    DegreeOneSmallComparisons.comparison0300
#print axioms sourceMap0300_checked
#print axioms fusedMap0300_checked
#print axioms certified0300
def sourceMap0300swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 6 2 1 v)
def fusedMap0300swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0300swap_checked : acceptsGraphIso
    (source (graph core0300) (root 6) 2 1) DegreeOneSmallSpectrum574.graph sourceMap0300swap=true := by decide +kernel
theorem fusedMap0300swap_checked : acceptsGraphIso
    (fused (graph core0300) (root 6) 2 1) DegreeOneSmallSpectrum392.graph fusedMap0300swap=true := by decide +kernel
theorem certified0300swap : Certified (graph core0300) (root 6) 2 1 :=
  of_native_maps core0300 DegreeOneSmallSpectrum574.graph DegreeOneSmallSpectrum392.graph
    sourceMap0300swap fusedMap0300swap sourceMap0300swap_checked fusedMap0300swap_checked
    DegreeOneSmallComparisons.comparison0300
#print axioms sourceMap0300swap_checked
#print axioms fusedMap0300swap_checked
#print axioms certified0300swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
