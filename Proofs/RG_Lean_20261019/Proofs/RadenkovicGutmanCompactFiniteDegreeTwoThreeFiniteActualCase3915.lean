/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3915 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap3915 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3915 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3915_checked : acceptsGraphIso
    (source (graph core3915) (root 8) 1 4) DegreeTwoThreeSpectrum4827.graph sourceMap3915=true := by decide +kernel
theorem fusedMap3915_checked : acceptsGraphIso
    (fused (graph core3915) (root 8) 1 4) DegreeTwoThreeSpectrum4461.graph fusedMap3915=true := by decide +kernel
theorem certified3915 : Certified (graph core3915) (root 8) 1 4 :=
  of_native_maps core3915 DegreeTwoThreeSpectrum4827.graph DegreeTwoThreeSpectrum4461.graph
    sourceMap3915 fusedMap3915 sourceMap3915_checked fusedMap3915_checked
    DegreeTwoThreeFiniteComparisons.comparison3915
#print axioms sourceMap3915_checked
#print axioms fusedMap3915_checked
#print axioms certified3915
def sourceMap3915swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3915swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3915swap_checked : acceptsGraphIso
    (source (graph core3915) (root 8) 4 1) DegreeTwoThreeSpectrum4827.graph sourceMap3915swap=true := by decide +kernel
theorem fusedMap3915swap_checked : acceptsGraphIso
    (fused (graph core3915) (root 8) 4 1) DegreeTwoThreeSpectrum4461.graph fusedMap3915swap=true := by decide +kernel
theorem certified3915swap : Certified (graph core3915) (root 8) 4 1 :=
  of_native_maps core3915 DegreeTwoThreeSpectrum4827.graph DegreeTwoThreeSpectrum4461.graph
    sourceMap3915swap fusedMap3915swap sourceMap3915swap_checked fusedMap3915swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3915
#print axioms sourceMap3915swap_checked
#print axioms fusedMap3915swap_checked
#print axioms certified3915swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
