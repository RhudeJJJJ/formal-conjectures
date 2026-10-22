/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2915 : Family 10 := level10.get ⟨1357,by decide⟩
def sourceMap2915 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2915 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2915_checked : acceptsGraphIso
    (source (graph core2915) (root 10) 0 4) DegreeTwoThreeSpectrum6691.graph sourceMap2915=true := by decide +kernel
theorem fusedMap2915_checked : acceptsGraphIso
    (fused (graph core2915) (root 10) 0 4) DegreeTwoThreeSpectrum6692.graph fusedMap2915=true := by decide +kernel
theorem certified2915 : Certified (graph core2915) (root 10) 0 4 :=
  of_native_maps core2915 DegreeTwoThreeSpectrum6691.graph DegreeTwoThreeSpectrum6692.graph
    sourceMap2915 fusedMap2915 sourceMap2915_checked fusedMap2915_checked
    DegreeTwoThreeFiniteComparisons.comparison2915
#print axioms sourceMap2915_checked
#print axioms fusedMap2915_checked
#print axioms certified2915
def sourceMap2915swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2915swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2915swap_checked : acceptsGraphIso
    (source (graph core2915) (root 10) 4 0) DegreeTwoThreeSpectrum6691.graph sourceMap2915swap=true := by decide +kernel
theorem fusedMap2915swap_checked : acceptsGraphIso
    (fused (graph core2915) (root 10) 4 0) DegreeTwoThreeSpectrum6692.graph fusedMap2915swap=true := by decide +kernel
theorem certified2915swap : Certified (graph core2915) (root 10) 4 0 :=
  of_native_maps core2915 DegreeTwoThreeSpectrum6691.graph DegreeTwoThreeSpectrum6692.graph
    sourceMap2915swap fusedMap2915swap sourceMap2915swap_checked fusedMap2915swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2915
#print axioms sourceMap2915swap_checked
#print axioms fusedMap2915swap_checked
#print axioms certified2915swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
