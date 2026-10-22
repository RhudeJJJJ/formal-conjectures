/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1080 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap1080 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (sourceLabel 7 0 2 v)
def fusedMap1080 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1080_checked : acceptsGraphIso
    (source (graph core1080) (root 7) 0 2) DegreeOneSmallSpectrum671.graph sourceMap1080=true := by decide +kernel
theorem fusedMap1080_checked : acceptsGraphIso
    (fused (graph core1080) (root 7) 0 2) DegreeOneSmallSpectrum412.graph fusedMap1080=true := by decide +kernel
theorem certified1080 : Certified (graph core1080) (root 7) 0 2 :=
  of_native_maps core1080 DegreeOneSmallSpectrum671.graph DegreeOneSmallSpectrum412.graph
    sourceMap1080 fusedMap1080 sourceMap1080_checked fusedMap1080_checked
    DegreeTwoThreeFiniteComparisons.comparison1080
#print axioms sourceMap1080_checked
#print axioms fusedMap1080_checked
#print axioms certified1080
def sourceMap1080swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11] (sourceLabel 7 2 0 v)
def fusedMap1080swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1080swap_checked : acceptsGraphIso
    (source (graph core1080) (root 7) 2 0) DegreeOneSmallSpectrum671.graph sourceMap1080swap=true := by decide +kernel
theorem fusedMap1080swap_checked : acceptsGraphIso
    (fused (graph core1080) (root 7) 2 0) DegreeOneSmallSpectrum412.graph fusedMap1080swap=true := by decide +kernel
theorem certified1080swap : Certified (graph core1080) (root 7) 2 0 :=
  of_native_maps core1080 DegreeOneSmallSpectrum671.graph DegreeOneSmallSpectrum412.graph
    sourceMap1080swap fusedMap1080swap sourceMap1080swap_checked fusedMap1080swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1080
#print axioms sourceMap1080swap_checked
#print axioms fusedMap1080swap_checked
#print axioms certified1080swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
