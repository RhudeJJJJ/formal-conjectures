/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1221 : Family 9 := level9.get ⟨128,by decide⟩
def sourceMap1221 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,7,8,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1221 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1221_checked : acceptsGraphIso
    (source (graph core1221) (root 9) 0 2) DegreeTwoThreeSpectrum1878.graph sourceMap1221=true := by decide +kernel
theorem fusedMap1221_checked : acceptsGraphIso
    (fused (graph core1221) (root 9) 0 2) DegreeTwoThreeSpectrum1922.graph fusedMap1221=true := by decide +kernel
theorem certified1221 : Certified (graph core1221) (root 9) 0 2 :=
  of_native_maps core1221 DegreeTwoThreeSpectrum1878.graph DegreeTwoThreeSpectrum1922.graph
    sourceMap1221 fusedMap1221 sourceMap1221_checked fusedMap1221_checked
    DegreeTwoThreeFiniteComparisons.comparison1221
#print axioms sourceMap1221_checked
#print axioms fusedMap1221_checked
#print axioms certified1221
def sourceMap1221swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,7,8,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1221swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1221swap_checked : acceptsGraphIso
    (source (graph core1221) (root 9) 2 0) DegreeTwoThreeSpectrum1878.graph sourceMap1221swap=true := by decide +kernel
theorem fusedMap1221swap_checked : acceptsGraphIso
    (fused (graph core1221) (root 9) 2 0) DegreeTwoThreeSpectrum1922.graph fusedMap1221swap=true := by decide +kernel
theorem certified1221swap : Certified (graph core1221) (root 9) 2 0 :=
  of_native_maps core1221 DegreeTwoThreeSpectrum1878.graph DegreeTwoThreeSpectrum1922.graph
    sourceMap1221swap fusedMap1221swap sourceMap1221swap_checked fusedMap1221swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1221
#print axioms sourceMap1221swap_checked
#print axioms fusedMap1221swap_checked
#print axioms certified1221swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
