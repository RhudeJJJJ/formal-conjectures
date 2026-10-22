/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2708 : Family 10 := level10.get ⟨842,by decide⟩
def sourceMap2708 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2708 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2708_checked : acceptsGraphIso
    (source (graph core2708) (root 10) 0 4) DegreeTwoThreeSpectrum6879.graph sourceMap2708=true := by decide +kernel
theorem fusedMap2708_checked : acceptsGraphIso
    (fused (graph core2708) (root 10) 0 4) DegreeTwoThreeSpectrum5674.graph fusedMap2708=true := by decide +kernel
theorem certified2708 : Certified (graph core2708) (root 10) 0 4 :=
  of_native_maps core2708 DegreeTwoThreeSpectrum6879.graph DegreeTwoThreeSpectrum5674.graph
    sourceMap2708 fusedMap2708 sourceMap2708_checked fusedMap2708_checked
    DegreeTwoThreeFiniteComparisons.comparison2708
#print axioms sourceMap2708_checked
#print axioms fusedMap2708_checked
#print axioms certified2708
def sourceMap2708swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2708swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2708swap_checked : acceptsGraphIso
    (source (graph core2708) (root 10) 4 0) DegreeTwoThreeSpectrum6879.graph sourceMap2708swap=true := by decide +kernel
theorem fusedMap2708swap_checked : acceptsGraphIso
    (fused (graph core2708) (root 10) 4 0) DegreeTwoThreeSpectrum5674.graph fusedMap2708swap=true := by decide +kernel
theorem certified2708swap : Certified (graph core2708) (root 10) 4 0 :=
  of_native_maps core2708 DegreeTwoThreeSpectrum6879.graph DegreeTwoThreeSpectrum5674.graph
    sourceMap2708swap fusedMap2708swap sourceMap2708swap_checked fusedMap2708swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2708
#print axioms sourceMap2708swap_checked
#print axioms fusedMap2708swap_checked
#print axioms certified2708swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
