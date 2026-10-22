/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1067 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap1067 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1067 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1067_checked : acceptsGraphIso
    (source (graph core1067) (root 7) 0 2) DegreeOneSmallSpectrum477.graph sourceMap1067=true := by decide +kernel
theorem fusedMap1067_checked : acceptsGraphIso
    (fused (graph core1067) (root 7) 0 2) DegreeOneSmallSpectrum479.graph fusedMap1067=true := by decide +kernel
theorem certified1067 : Certified (graph core1067) (root 7) 0 2 :=
  of_native_maps core1067 DegreeOneSmallSpectrum477.graph DegreeOneSmallSpectrum479.graph
    sourceMap1067 fusedMap1067 sourceMap1067_checked fusedMap1067_checked
    DegreeTwoThreeFiniteComparisons.comparison1067
#print axioms sourceMap1067_checked
#print axioms fusedMap1067_checked
#print axioms certified1067
def sourceMap1067swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1067swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1067swap_checked : acceptsGraphIso
    (source (graph core1067) (root 7) 2 0) DegreeOneSmallSpectrum477.graph sourceMap1067swap=true := by decide +kernel
theorem fusedMap1067swap_checked : acceptsGraphIso
    (fused (graph core1067) (root 7) 2 0) DegreeOneSmallSpectrum479.graph fusedMap1067swap=true := by decide +kernel
theorem certified1067swap : Certified (graph core1067) (root 7) 2 0 :=
  of_native_maps core1067 DegreeOneSmallSpectrum477.graph DegreeOneSmallSpectrum479.graph
    sourceMap1067swap fusedMap1067swap sourceMap1067swap_checked fusedMap1067swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1067
#print axioms sourceMap1067swap_checked
#print axioms fusedMap1067swap_checked
#print axioms certified1067swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
