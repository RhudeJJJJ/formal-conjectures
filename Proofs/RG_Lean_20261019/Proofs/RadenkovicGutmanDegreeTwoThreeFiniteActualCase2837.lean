/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2837 : Family 10 := level10.get ⟨1167,by decide⟩
def sourceMap2837 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2837 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2837_checked : acceptsGraphIso
    (source (graph core2837) (root 10) 0 4) DegreeTwoThreeSpectrum6317.graph sourceMap2837=true := by decide +kernel
theorem fusedMap2837_checked : acceptsGraphIso
    (fused (graph core2837) (root 10) 0 4) DegreeTwoThreeSpectrum6318.graph fusedMap2837=true := by decide +kernel
theorem certified2837 : Certified (graph core2837) (root 10) 0 4 :=
  of_native_maps core2837 DegreeTwoThreeSpectrum6317.graph DegreeTwoThreeSpectrum6318.graph
    sourceMap2837 fusedMap2837 sourceMap2837_checked fusedMap2837_checked
    DegreeTwoThreeFiniteComparisons.comparison2837
#print axioms sourceMap2837_checked
#print axioms fusedMap2837_checked
#print axioms certified2837
def sourceMap2837swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2837swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2837swap_checked : acceptsGraphIso
    (source (graph core2837) (root 10) 4 0) DegreeTwoThreeSpectrum6317.graph sourceMap2837swap=true := by decide +kernel
theorem fusedMap2837swap_checked : acceptsGraphIso
    (fused (graph core2837) (root 10) 4 0) DegreeTwoThreeSpectrum6318.graph fusedMap2837swap=true := by decide +kernel
theorem certified2837swap : Certified (graph core2837) (root 10) 4 0 :=
  of_native_maps core2837 DegreeTwoThreeSpectrum6317.graph DegreeTwoThreeSpectrum6318.graph
    sourceMap2837swap fusedMap2837swap sourceMap2837swap_checked fusedMap2837swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2837
#print axioms sourceMap2837swap_checked
#print axioms fusedMap2837swap_checked
#print axioms certified2837swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
