/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2654 : Family 10 := level10.get ⟨690,by decide⟩
def sourceMap2654 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2654 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2654_checked : acceptsGraphIso
    (source (graph core2654) (root 10) 0 4) DegreeTwoThreeSpectrum6502.graph sourceMap2654=true := by decide +kernel
theorem fusedMap2654_checked : acceptsGraphIso
    (fused (graph core2654) (root 10) 0 4) DegreeTwoThreeSpectrum5426.graph fusedMap2654=true := by decide +kernel
theorem certified2654 : Certified (graph core2654) (root 10) 0 4 :=
  of_native_maps core2654 DegreeTwoThreeSpectrum6502.graph DegreeTwoThreeSpectrum5426.graph
    sourceMap2654 fusedMap2654 sourceMap2654_checked fusedMap2654_checked
    DegreeTwoThreeFiniteComparisons.comparison2654
#print axioms sourceMap2654_checked
#print axioms fusedMap2654_checked
#print axioms certified2654
def sourceMap2654swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2654swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2654swap_checked : acceptsGraphIso
    (source (graph core2654) (root 10) 4 0) DegreeTwoThreeSpectrum6502.graph sourceMap2654swap=true := by decide +kernel
theorem fusedMap2654swap_checked : acceptsGraphIso
    (fused (graph core2654) (root 10) 4 0) DegreeTwoThreeSpectrum5426.graph fusedMap2654swap=true := by decide +kernel
theorem certified2654swap : Certified (graph core2654) (root 10) 4 0 :=
  of_native_maps core2654 DegreeTwoThreeSpectrum6502.graph DegreeTwoThreeSpectrum5426.graph
    sourceMap2654swap fusedMap2654swap sourceMap2654swap_checked fusedMap2654swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2654
#print axioms sourceMap2654swap_checked
#print axioms fusedMap2654swap_checked
#print axioms certified2654swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
