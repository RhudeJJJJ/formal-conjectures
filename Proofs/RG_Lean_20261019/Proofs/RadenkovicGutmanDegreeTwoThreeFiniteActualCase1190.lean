/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1190 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap1190 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 0 2 v)
def fusedMap1190 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1190_checked : acceptsGraphIso
    (source (graph core1190) (root 8) 0 2) DegreeOneSmallSpectrum1555.graph sourceMap1190=true := by decide +kernel
theorem fusedMap1190_checked : acceptsGraphIso
    (fused (graph core1190) (root 8) 0 2) DegreeOneSmallSpectrum1558.graph fusedMap1190=true := by decide +kernel
theorem certified1190 : Certified (graph core1190) (root 8) 0 2 :=
  of_native_maps core1190 DegreeOneSmallSpectrum1555.graph DegreeOneSmallSpectrum1558.graph
    sourceMap1190 fusedMap1190 sourceMap1190_checked fusedMap1190_checked
    DegreeTwoThreeFiniteComparisons.comparison1190
#print axioms sourceMap1190_checked
#print axioms fusedMap1190_checked
#print axioms certified1190
def sourceMap1190swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,9] (sourceLabel 8 2 0 v)
def fusedMap1190swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1190swap_checked : acceptsGraphIso
    (source (graph core1190) (root 8) 2 0) DegreeOneSmallSpectrum1555.graph sourceMap1190swap=true := by decide +kernel
theorem fusedMap1190swap_checked : acceptsGraphIso
    (fused (graph core1190) (root 8) 2 0) DegreeOneSmallSpectrum1558.graph fusedMap1190swap=true := by decide +kernel
theorem certified1190swap : Certified (graph core1190) (root 8) 2 0 :=
  of_native_maps core1190 DegreeOneSmallSpectrum1555.graph DegreeOneSmallSpectrum1558.graph
    sourceMap1190swap fusedMap1190swap sourceMap1190swap_checked fusedMap1190swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1190
#print axioms sourceMap1190swap_checked
#print axioms fusedMap1190swap_checked
#print axioms certified1190swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
