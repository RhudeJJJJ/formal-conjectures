/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2822 : Family 10 := level10.get ⟨1132,by decide⟩
def sourceMap2822 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2822 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2822_checked : acceptsGraphIso
    (source (graph core2822) (root 10) 0 4) DegreeTwoThreeSpectrum6250.graph sourceMap2822=true := by decide +kernel
theorem fusedMap2822_checked : acceptsGraphIso
    (fused (graph core2822) (root 10) 0 4) DegreeTwoThreeSpectrum6251.graph fusedMap2822=true := by decide +kernel
theorem certified2822 : Certified (graph core2822) (root 10) 0 4 :=
  of_native_maps core2822 DegreeTwoThreeSpectrum6250.graph DegreeTwoThreeSpectrum6251.graph
    sourceMap2822 fusedMap2822 sourceMap2822_checked fusedMap2822_checked
    DegreeTwoThreeFiniteComparisons.comparison2822
#print axioms sourceMap2822_checked
#print axioms fusedMap2822_checked
#print axioms certified2822
def sourceMap2822swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2822swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2822swap_checked : acceptsGraphIso
    (source (graph core2822) (root 10) 4 0) DegreeTwoThreeSpectrum6250.graph sourceMap2822swap=true := by decide +kernel
theorem fusedMap2822swap_checked : acceptsGraphIso
    (fused (graph core2822) (root 10) 4 0) DegreeTwoThreeSpectrum6251.graph fusedMap2822swap=true := by decide +kernel
theorem certified2822swap : Certified (graph core2822) (root 10) 4 0 :=
  of_native_maps core2822 DegreeTwoThreeSpectrum6250.graph DegreeTwoThreeSpectrum6251.graph
    sourceMap2822swap fusedMap2822swap sourceMap2822swap_checked fusedMap2822swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2822
#print axioms sourceMap2822swap_checked
#print axioms fusedMap2822swap_checked
#print axioms certified2822swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
