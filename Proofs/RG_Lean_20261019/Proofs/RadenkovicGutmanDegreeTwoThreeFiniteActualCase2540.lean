/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2540 : Family 10 := level10.get ⟨352,by decide⟩
def sourceMap2540 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2540 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2540_checked : acceptsGraphIso
    (source (graph core2540) (root 10) 0 4) DegreeTwoThreeSpectrum5624.graph sourceMap2540=true := by decide +kernel
theorem fusedMap2540_checked : acceptsGraphIso
    (fused (graph core2540) (root 10) 0 4) DegreeTwoThreeSpectrum5625.graph fusedMap2540=true := by decide +kernel
theorem certified2540 : Certified (graph core2540) (root 10) 0 4 :=
  of_native_maps core2540 DegreeTwoThreeSpectrum5624.graph DegreeTwoThreeSpectrum5625.graph
    sourceMap2540 fusedMap2540 sourceMap2540_checked fusedMap2540_checked
    DegreeTwoThreeFiniteComparisons.comparison2540
#print axioms sourceMap2540_checked
#print axioms fusedMap2540_checked
#print axioms certified2540
def sourceMap2540swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2540swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2540swap_checked : acceptsGraphIso
    (source (graph core2540) (root 10) 4 0) DegreeTwoThreeSpectrum5624.graph sourceMap2540swap=true := by decide +kernel
theorem fusedMap2540swap_checked : acceptsGraphIso
    (fused (graph core2540) (root 10) 4 0) DegreeTwoThreeSpectrum5625.graph fusedMap2540swap=true := by decide +kernel
theorem certified2540swap : Certified (graph core2540) (root 10) 4 0 :=
  of_native_maps core2540 DegreeTwoThreeSpectrum5624.graph DegreeTwoThreeSpectrum5625.graph
    sourceMap2540swap fusedMap2540swap sourceMap2540swap_checked fusedMap2540swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2540
#print axioms sourceMap2540swap_checked
#print axioms fusedMap2540swap_checked
#print axioms certified2540swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
