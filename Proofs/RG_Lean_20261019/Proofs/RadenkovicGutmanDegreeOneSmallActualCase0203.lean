/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0203 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0203 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (sourceLabel 5 1 3 v)
def fusedMap0203 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0203_checked : acceptsGraphIso
    (source (graph core0203) (root 5) 1 3) DegreeOneSmallSpectrum583.graph sourceMap0203=true := by decide +kernel
theorem fusedMap0203_checked : acceptsGraphIso
    (fused (graph core0203) (root 5) 1 3) DegreeOneSmallSpectrum392.graph fusedMap0203=true := by decide +kernel
theorem certified0203 : Certified (graph core0203) (root 5) 1 3 :=
  of_native_maps core0203 DegreeOneSmallSpectrum583.graph DegreeOneSmallSpectrum392.graph
    sourceMap0203 fusedMap0203 sourceMap0203_checked fusedMap0203_checked
    DegreeOneSmallComparisons.comparison0203
#print axioms sourceMap0203_checked
#print axioms fusedMap0203_checked
#print axioms certified0203
def sourceMap0203swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 3 1 v)
def fusedMap0203swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0203swap_checked : acceptsGraphIso
    (source (graph core0203) (root 5) 3 1) DegreeOneSmallSpectrum583.graph sourceMap0203swap=true := by decide +kernel
theorem fusedMap0203swap_checked : acceptsGraphIso
    (fused (graph core0203) (root 5) 3 1) DegreeOneSmallSpectrum392.graph fusedMap0203swap=true := by decide +kernel
theorem certified0203swap : Certified (graph core0203) (root 5) 3 1 :=
  of_native_maps core0203 DegreeOneSmallSpectrum583.graph DegreeOneSmallSpectrum392.graph
    sourceMap0203swap fusedMap0203swap sourceMap0203swap_checked fusedMap0203swap_checked
    DegreeOneSmallComparisons.comparison0203
#print axioms sourceMap0203swap_checked
#print axioms fusedMap0203swap_checked
#print axioms certified0203swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
