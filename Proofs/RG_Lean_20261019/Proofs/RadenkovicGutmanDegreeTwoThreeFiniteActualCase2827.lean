/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2827 : Family 10 := level10.get ⟨1143,by decide⟩
def sourceMap2827 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2827 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2827_checked : acceptsGraphIso
    (source (graph core2827) (root 10) 0 4) DegreeTwoThreeSpectrum6272.graph sourceMap2827=true := by decide +kernel
theorem fusedMap2827_checked : acceptsGraphIso
    (fused (graph core2827) (root 10) 0 4) DegreeTwoThreeSpectrum6273.graph fusedMap2827=true := by decide +kernel
theorem certified2827 : Certified (graph core2827) (root 10) 0 4 :=
  of_native_maps core2827 DegreeTwoThreeSpectrum6272.graph DegreeTwoThreeSpectrum6273.graph
    sourceMap2827 fusedMap2827 sourceMap2827_checked fusedMap2827_checked
    DegreeTwoThreeFiniteComparisons.comparison2827
#print axioms sourceMap2827_checked
#print axioms fusedMap2827_checked
#print axioms certified2827
def sourceMap2827swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2827swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2827swap_checked : acceptsGraphIso
    (source (graph core2827) (root 10) 4 0) DegreeTwoThreeSpectrum6272.graph sourceMap2827swap=true := by decide +kernel
theorem fusedMap2827swap_checked : acceptsGraphIso
    (fused (graph core2827) (root 10) 4 0) DegreeTwoThreeSpectrum6273.graph fusedMap2827swap=true := by decide +kernel
theorem certified2827swap : Certified (graph core2827) (root 10) 4 0 :=
  of_native_maps core2827 DegreeTwoThreeSpectrum6272.graph DegreeTwoThreeSpectrum6273.graph
    sourceMap2827swap fusedMap2827swap sourceMap2827swap_checked fusedMap2827swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2827
#print axioms sourceMap2827swap_checked
#print axioms fusedMap2827swap_checked
#print axioms certified2827swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
