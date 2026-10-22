/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1132 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap1132 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1132 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1132_checked : acceptsGraphIso
    (source (graph core1132) (root 8) 0 2) DegreeOneSmallSpectrum1241.graph sourceMap1132=true := by decide +kernel
theorem fusedMap1132_checked : acceptsGraphIso
    (fused (graph core1132) (root 8) 0 2) DegreeOneSmallSpectrum1246.graph fusedMap1132=true := by decide +kernel
theorem certified1132 : Certified (graph core1132) (root 8) 0 2 :=
  of_native_maps core1132 DegreeOneSmallSpectrum1241.graph DegreeOneSmallSpectrum1246.graph
    sourceMap1132 fusedMap1132 sourceMap1132_checked fusedMap1132_checked
    DegreeTwoThreeFiniteComparisons.comparison1132
#print axioms sourceMap1132_checked
#print axioms fusedMap1132_checked
#print axioms certified1132
def sourceMap1132swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1132swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1132swap_checked : acceptsGraphIso
    (source (graph core1132) (root 8) 2 0) DegreeOneSmallSpectrum1241.graph sourceMap1132swap=true := by decide +kernel
theorem fusedMap1132swap_checked : acceptsGraphIso
    (fused (graph core1132) (root 8) 2 0) DegreeOneSmallSpectrum1246.graph fusedMap1132swap=true := by decide +kernel
theorem certified1132swap : Certified (graph core1132) (root 8) 2 0 :=
  of_native_maps core1132 DegreeOneSmallSpectrum1241.graph DegreeOneSmallSpectrum1246.graph
    sourceMap1132swap fusedMap1132swap sourceMap1132swap_checked fusedMap1132swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1132
#print axioms sourceMap1132swap_checked
#print axioms fusedMap1132swap_checked
#print axioms certified1132swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
