/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1391 : Family 9 := level9.get ⟨577,by decide⟩
def sourceMap1391 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1391 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1391_checked : acceptsGraphIso
    (source (graph core1391) (root 9) 0 2) DegreeTwoThreeSpectrum2262.graph sourceMap1391=true := by decide +kernel
theorem fusedMap1391_checked : acceptsGraphIso
    (fused (graph core1391) (root 9) 0 2) DegreeTwoThreeSpectrum1969.graph fusedMap1391=true := by decide +kernel
theorem certified1391 : Certified (graph core1391) (root 9) 0 2 :=
  of_native_maps core1391 DegreeTwoThreeSpectrum2262.graph DegreeTwoThreeSpectrum1969.graph
    sourceMap1391 fusedMap1391 sourceMap1391_checked fusedMap1391_checked
    DegreeTwoThreeFiniteComparisons.comparison1391
#print axioms sourceMap1391_checked
#print axioms fusedMap1391_checked
#print axioms certified1391
def sourceMap1391swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1391swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1391swap_checked : acceptsGraphIso
    (source (graph core1391) (root 9) 2 0) DegreeTwoThreeSpectrum2262.graph sourceMap1391swap=true := by decide +kernel
theorem fusedMap1391swap_checked : acceptsGraphIso
    (fused (graph core1391) (root 9) 2 0) DegreeTwoThreeSpectrum1969.graph fusedMap1391swap=true := by decide +kernel
theorem certified1391swap : Certified (graph core1391) (root 9) 2 0 :=
  of_native_maps core1391 DegreeTwoThreeSpectrum2262.graph DegreeTwoThreeSpectrum1969.graph
    sourceMap1391swap fusedMap1391swap sourceMap1391swap_checked fusedMap1391swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1391
#print axioms sourceMap1391swap_checked
#print axioms fusedMap1391swap_checked
#print axioms certified1391swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
