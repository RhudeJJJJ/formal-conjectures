/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1265 : Family 9 := level9.get ⟨264,by decide⟩
def sourceMap1265 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1265 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1265_checked : acceptsGraphIso
    (source (graph core1265) (root 9) 0 2) DegreeTwoThreeSpectrum2215.graph sourceMap1265=true := by decide +kernel
theorem fusedMap1265_checked : acceptsGraphIso
    (fused (graph core1265) (root 9) 0 2) DegreeTwoThreeSpectrum1872.graph fusedMap1265=true := by decide +kernel
theorem certified1265 : Certified (graph core1265) (root 9) 0 2 :=
  of_native_maps core1265 DegreeTwoThreeSpectrum2215.graph DegreeTwoThreeSpectrum1872.graph
    sourceMap1265 fusedMap1265 sourceMap1265_checked fusedMap1265_checked
    DegreeTwoThreeFiniteComparisons.comparison1265
#print axioms sourceMap1265_checked
#print axioms fusedMap1265_checked
#print axioms certified1265
def sourceMap1265swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1265swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1265swap_checked : acceptsGraphIso
    (source (graph core1265) (root 9) 2 0) DegreeTwoThreeSpectrum2215.graph sourceMap1265swap=true := by decide +kernel
theorem fusedMap1265swap_checked : acceptsGraphIso
    (fused (graph core1265) (root 9) 2 0) DegreeTwoThreeSpectrum1872.graph fusedMap1265swap=true := by decide +kernel
theorem certified1265swap : Certified (graph core1265) (root 9) 2 0 :=
  of_native_maps core1265 DegreeTwoThreeSpectrum2215.graph DegreeTwoThreeSpectrum1872.graph
    sourceMap1265swap fusedMap1265swap sourceMap1265swap_checked fusedMap1265swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1265
#print axioms sourceMap1265swap_checked
#print axioms fusedMap1265swap_checked
#print axioms certified1265swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
