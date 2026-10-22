/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1240 : Family 9 := level9.get ⟨190,by decide⟩
def sourceMap1240 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,11,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1240 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1240_checked : acceptsGraphIso
    (source (graph core1240) (root 9) 0 2) DegreeTwoThreeSpectrum2072.graph sourceMap1240=true := by decide +kernel
theorem fusedMap1240_checked : acceptsGraphIso
    (fused (graph core1240) (root 9) 0 2) DegreeTwoThreeSpectrum1789.graph fusedMap1240=true := by decide +kernel
theorem certified1240 : Certified (graph core1240) (root 9) 0 2 :=
  of_native_maps core1240 DegreeTwoThreeSpectrum2072.graph DegreeTwoThreeSpectrum1789.graph
    sourceMap1240 fusedMap1240 sourceMap1240_checked fusedMap1240_checked
    DegreeTwoThreeFiniteComparisons.comparison1240
#print axioms sourceMap1240_checked
#print axioms fusedMap1240_checked
#print axioms certified1240
def sourceMap1240swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,7,8,9,11] (sourceLabel 9 2 0 v)
def fusedMap1240swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1240swap_checked : acceptsGraphIso
    (source (graph core1240) (root 9) 2 0) DegreeTwoThreeSpectrum2072.graph sourceMap1240swap=true := by decide +kernel
theorem fusedMap1240swap_checked : acceptsGraphIso
    (fused (graph core1240) (root 9) 2 0) DegreeTwoThreeSpectrum1789.graph fusedMap1240swap=true := by decide +kernel
theorem certified1240swap : Certified (graph core1240) (root 9) 2 0 :=
  of_native_maps core1240 DegreeTwoThreeSpectrum2072.graph DegreeTwoThreeSpectrum1789.graph
    sourceMap1240swap fusedMap1240swap sourceMap1240swap_checked fusedMap1240swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1240
#print axioms sourceMap1240swap_checked
#print axioms fusedMap1240swap_checked
#print axioms certified1240swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
