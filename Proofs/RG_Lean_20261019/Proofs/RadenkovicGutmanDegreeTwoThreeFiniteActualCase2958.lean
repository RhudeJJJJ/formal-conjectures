/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2958 : Family 10 := level10.get ⟨1451,by decide⟩
def sourceMap2958 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2958 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2958_checked : acceptsGraphIso
    (source (graph core2958) (root 10) 0 4) DegreeTwoThreeSpectrum6919.graph sourceMap2958=true := by decide +kernel
theorem fusedMap2958_checked : acceptsGraphIso
    (fused (graph core2958) (root 10) 0 4) DegreeTwoThreeSpectrum6920.graph fusedMap2958=true := by decide +kernel
theorem certified2958 : Certified (graph core2958) (root 10) 0 4 :=
  of_native_maps core2958 DegreeTwoThreeSpectrum6919.graph DegreeTwoThreeSpectrum6920.graph
    sourceMap2958 fusedMap2958 sourceMap2958_checked fusedMap2958_checked
    DegreeTwoThreeFiniteComparisons.comparison2958
#print axioms sourceMap2958_checked
#print axioms fusedMap2958_checked
#print axioms certified2958
def sourceMap2958swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2958swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2958swap_checked : acceptsGraphIso
    (source (graph core2958) (root 10) 4 0) DegreeTwoThreeSpectrum6919.graph sourceMap2958swap=true := by decide +kernel
theorem fusedMap2958swap_checked : acceptsGraphIso
    (fused (graph core2958) (root 10) 4 0) DegreeTwoThreeSpectrum6920.graph fusedMap2958swap=true := by decide +kernel
theorem certified2958swap : Certified (graph core2958) (root 10) 4 0 :=
  of_native_maps core2958 DegreeTwoThreeSpectrum6919.graph DegreeTwoThreeSpectrum6920.graph
    sourceMap2958swap fusedMap2958swap sourceMap2958swap_checked fusedMap2958swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2958
#print axioms sourceMap2958swap_checked
#print axioms fusedMap2958swap_checked
#print axioms certified2958swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
