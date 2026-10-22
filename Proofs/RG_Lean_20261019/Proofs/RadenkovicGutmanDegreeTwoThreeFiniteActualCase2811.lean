/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2811 : Family 10 := level10.get ⟨1105,by decide⟩
def sourceMap2811 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2811 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2811_checked : acceptsGraphIso
    (source (graph core2811) (root 10) 0 4) DegreeTwoThreeSpectrum6194.graph sourceMap2811=true := by decide +kernel
theorem fusedMap2811_checked : acceptsGraphIso
    (fused (graph core2811) (root 10) 0 4) DegreeTwoThreeSpectrum6195.graph fusedMap2811=true := by decide +kernel
theorem certified2811 : Certified (graph core2811) (root 10) 0 4 :=
  of_native_maps core2811 DegreeTwoThreeSpectrum6194.graph DegreeTwoThreeSpectrum6195.graph
    sourceMap2811 fusedMap2811 sourceMap2811_checked fusedMap2811_checked
    DegreeTwoThreeFiniteComparisons.comparison2811
#print axioms sourceMap2811_checked
#print axioms fusedMap2811_checked
#print axioms certified2811
def sourceMap2811swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2811swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2811swap_checked : acceptsGraphIso
    (source (graph core2811) (root 10) 4 0) DegreeTwoThreeSpectrum6194.graph sourceMap2811swap=true := by decide +kernel
theorem fusedMap2811swap_checked : acceptsGraphIso
    (fused (graph core2811) (root 10) 4 0) DegreeTwoThreeSpectrum6195.graph fusedMap2811swap=true := by decide +kernel
theorem certified2811swap : Certified (graph core2811) (root 10) 4 0 :=
  of_native_maps core2811 DegreeTwoThreeSpectrum6194.graph DegreeTwoThreeSpectrum6195.graph
    sourceMap2811swap fusedMap2811swap sourceMap2811swap_checked fusedMap2811swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2811
#print axioms sourceMap2811swap_checked
#print axioms fusedMap2811swap_checked
#print axioms certified2811swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
