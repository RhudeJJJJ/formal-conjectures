/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1172 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap1172 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 8 0 2 v)
def fusedMap1172 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1172_checked : acceptsGraphIso
    (source (graph core1172) (root 8) 0 2) DegreeOneSmallSpectrum1835.graph sourceMap1172=true := by decide +kernel
theorem fusedMap1172_checked : acceptsGraphIso
    (fused (graph core1172) (root 8) 0 2) DegreeOneSmallSpectrum1137.graph fusedMap1172=true := by decide +kernel
theorem certified1172 : Certified (graph core1172) (root 8) 0 2 :=
  of_native_maps core1172 DegreeOneSmallSpectrum1835.graph DegreeOneSmallSpectrum1137.graph
    sourceMap1172 fusedMap1172 sourceMap1172_checked fusedMap1172_checked
    DegreeTwoThreeFiniteComparisons.comparison1172
#print axioms sourceMap1172_checked
#print axioms fusedMap1172_checked
#print axioms certified1172
def sourceMap1172swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8,12] (sourceLabel 8 2 0 v)
def fusedMap1172swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1172swap_checked : acceptsGraphIso
    (source (graph core1172) (root 8) 2 0) DegreeOneSmallSpectrum1835.graph sourceMap1172swap=true := by decide +kernel
theorem fusedMap1172swap_checked : acceptsGraphIso
    (fused (graph core1172) (root 8) 2 0) DegreeOneSmallSpectrum1137.graph fusedMap1172swap=true := by decide +kernel
theorem certified1172swap : Certified (graph core1172) (root 8) 2 0 :=
  of_native_maps core1172 DegreeOneSmallSpectrum1835.graph DegreeOneSmallSpectrum1137.graph
    sourceMap1172swap fusedMap1172swap sourceMap1172swap_checked fusedMap1172swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1172
#print axioms sourceMap1172swap_checked
#print axioms fusedMap1172swap_checked
#print axioms certified1172swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
