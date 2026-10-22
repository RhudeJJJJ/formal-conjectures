/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2647 : Family 10 := level10.get ⟨670,by decide⟩
def sourceMap2647 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2647 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2647_checked : acceptsGraphIso
    (source (graph core2647) (root 10) 0 4) DegreeTwoThreeSpectrum6452.graph sourceMap2647=true := by decide +kernel
theorem fusedMap2647_checked : acceptsGraphIso
    (fused (graph core2647) (root 10) 0 4) DegreeTwoThreeSpectrum5385.graph fusedMap2647=true := by decide +kernel
theorem certified2647 : Certified (graph core2647) (root 10) 0 4 :=
  of_native_maps core2647 DegreeTwoThreeSpectrum6452.graph DegreeTwoThreeSpectrum5385.graph
    sourceMap2647 fusedMap2647 sourceMap2647_checked fusedMap2647_checked
    DegreeTwoThreeFiniteComparisons.comparison2647
#print axioms sourceMap2647_checked
#print axioms fusedMap2647_checked
#print axioms certified2647
def sourceMap2647swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2647swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2647swap_checked : acceptsGraphIso
    (source (graph core2647) (root 10) 4 0) DegreeTwoThreeSpectrum6452.graph sourceMap2647swap=true := by decide +kernel
theorem fusedMap2647swap_checked : acceptsGraphIso
    (fused (graph core2647) (root 10) 4 0) DegreeTwoThreeSpectrum5385.graph fusedMap2647swap=true := by decide +kernel
theorem certified2647swap : Certified (graph core2647) (root 10) 4 0 :=
  of_native_maps core2647 DegreeTwoThreeSpectrum6452.graph DegreeTwoThreeSpectrum5385.graph
    sourceMap2647swap fusedMap2647swap sourceMap2647swap_checked fusedMap2647swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2647
#print axioms sourceMap2647swap_checked
#print axioms fusedMap2647swap_checked
#print axioms certified2647swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
