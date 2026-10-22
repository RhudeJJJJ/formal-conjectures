/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2865 : Family 10 := level10.get ⟨1228,by decide⟩
def sourceMap2865 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2865 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2865_checked : acceptsGraphIso
    (source (graph core2865) (root 10) 0 4) DegreeTwoThreeSpectrum6430.graph sourceMap2865=true := by decide +kernel
theorem fusedMap2865_checked : acceptsGraphIso
    (fused (graph core2865) (root 10) 0 4) DegreeTwoThreeSpectrum6431.graph fusedMap2865=true := by decide +kernel
theorem certified2865 : Certified (graph core2865) (root 10) 0 4 :=
  of_native_maps core2865 DegreeTwoThreeSpectrum6430.graph DegreeTwoThreeSpectrum6431.graph
    sourceMap2865 fusedMap2865 sourceMap2865_checked fusedMap2865_checked
    DegreeTwoThreeFiniteComparisons.comparison2865
#print axioms sourceMap2865_checked
#print axioms fusedMap2865_checked
#print axioms certified2865
def sourceMap2865swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2865swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2865swap_checked : acceptsGraphIso
    (source (graph core2865) (root 10) 4 0) DegreeTwoThreeSpectrum6430.graph sourceMap2865swap=true := by decide +kernel
theorem fusedMap2865swap_checked : acceptsGraphIso
    (fused (graph core2865) (root 10) 4 0) DegreeTwoThreeSpectrum6431.graph fusedMap2865swap=true := by decide +kernel
theorem certified2865swap : Certified (graph core2865) (root 10) 4 0 :=
  of_native_maps core2865 DegreeTwoThreeSpectrum6430.graph DegreeTwoThreeSpectrum6431.graph
    sourceMap2865swap fusedMap2865swap sourceMap2865swap_checked fusedMap2865swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2865
#print axioms sourceMap2865swap_checked
#print axioms fusedMap2865swap_checked
#print axioms certified2865swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
