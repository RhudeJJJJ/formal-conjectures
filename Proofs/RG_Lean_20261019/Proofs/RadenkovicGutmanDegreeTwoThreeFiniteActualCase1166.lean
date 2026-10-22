/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1166 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap1166 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1166 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1166_checked : acceptsGraphIso
    (source (graph core1166) (root 8) 0 2) DegreeOneSmallSpectrum1722.graph sourceMap1166=true := by decide +kernel
theorem fusedMap1166_checked : acceptsGraphIso
    (fused (graph core1166) (root 8) 0 2) DegreeOneSmallSpectrum1084.graph fusedMap1166=true := by decide +kernel
theorem certified1166 : Certified (graph core1166) (root 8) 0 2 :=
  of_native_maps core1166 DegreeOneSmallSpectrum1722.graph DegreeOneSmallSpectrum1084.graph
    sourceMap1166 fusedMap1166 sourceMap1166_checked fusedMap1166_checked
    DegreeTwoThreeFiniteComparisons.comparison1166
#print axioms sourceMap1166_checked
#print axioms fusedMap1166_checked
#print axioms certified1166
def sourceMap1166swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1166swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1166swap_checked : acceptsGraphIso
    (source (graph core1166) (root 8) 2 0) DegreeOneSmallSpectrum1722.graph sourceMap1166swap=true := by decide +kernel
theorem fusedMap1166swap_checked : acceptsGraphIso
    (fused (graph core1166) (root 8) 2 0) DegreeOneSmallSpectrum1084.graph fusedMap1166swap=true := by decide +kernel
theorem certified1166swap : Certified (graph core1166) (root 8) 2 0 :=
  of_native_maps core1166 DegreeOneSmallSpectrum1722.graph DegreeOneSmallSpectrum1084.graph
    sourceMap1166swap fusedMap1166swap sourceMap1166swap_checked fusedMap1166swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1166
#print axioms sourceMap1166swap_checked
#print axioms fusedMap1166swap_checked
#print axioms certified1166swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
