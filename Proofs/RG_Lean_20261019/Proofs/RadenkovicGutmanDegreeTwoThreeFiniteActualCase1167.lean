/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1167 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap1167 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1167 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1167_checked : acceptsGraphIso
    (source (graph core1167) (root 8) 0 2) DegreeOneSmallSpectrum1754.graph sourceMap1167=true := by decide +kernel
theorem fusedMap1167_checked : acceptsGraphIso
    (fused (graph core1167) (root 8) 0 2) DegreeOneSmallSpectrum1091.graph fusedMap1167=true := by decide +kernel
theorem certified1167 : Certified (graph core1167) (root 8) 0 2 :=
  of_native_maps core1167 DegreeOneSmallSpectrum1754.graph DegreeOneSmallSpectrum1091.graph
    sourceMap1167 fusedMap1167 sourceMap1167_checked fusedMap1167_checked
    DegreeTwoThreeFiniteComparisons.comparison1167
#print axioms sourceMap1167_checked
#print axioms fusedMap1167_checked
#print axioms certified1167
def sourceMap1167swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1167swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1167swap_checked : acceptsGraphIso
    (source (graph core1167) (root 8) 2 0) DegreeOneSmallSpectrum1754.graph sourceMap1167swap=true := by decide +kernel
theorem fusedMap1167swap_checked : acceptsGraphIso
    (fused (graph core1167) (root 8) 2 0) DegreeOneSmallSpectrum1091.graph fusedMap1167swap=true := by decide +kernel
theorem certified1167swap : Certified (graph core1167) (root 8) 2 0 :=
  of_native_maps core1167 DegreeOneSmallSpectrum1754.graph DegreeOneSmallSpectrum1091.graph
    sourceMap1167swap fusedMap1167swap sourceMap1167swap_checked fusedMap1167swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1167
#print axioms sourceMap1167swap_checked
#print axioms fusedMap1167swap_checked
#print axioms certified1167swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
