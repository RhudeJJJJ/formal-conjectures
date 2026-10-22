/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2048 : Family 10 := level10.get ⟨1801,by decide⟩
def sourceMap2048 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 0 2 v)
def fusedMap2048 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2048_checked : acceptsGraphIso
    (source (graph core2048) (root 10) 0 2) DegreeTwoThreeSpectrum3731.graph sourceMap2048=true := by decide +kernel
theorem fusedMap2048_checked : acceptsGraphIso
    (fused (graph core2048) (root 10) 0 2) DegreeTwoThreeSpectrum3732.graph fusedMap2048=true := by decide +kernel
theorem certified2048 : Certified (graph core2048) (root 10) 0 2 :=
  of_native_maps core2048 DegreeTwoThreeSpectrum3731.graph DegreeTwoThreeSpectrum3732.graph
    sourceMap2048 fusedMap2048 sourceMap2048_checked fusedMap2048_checked
    DegreeTwoThreeFiniteComparisons.comparison2048
#print axioms sourceMap2048_checked
#print axioms fusedMap2048_checked
#print axioms certified2048
def sourceMap2048swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,11] (sourceLabel 10 2 0 v)
def fusedMap2048swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2048swap_checked : acceptsGraphIso
    (source (graph core2048) (root 10) 2 0) DegreeTwoThreeSpectrum3731.graph sourceMap2048swap=true := by decide +kernel
theorem fusedMap2048swap_checked : acceptsGraphIso
    (fused (graph core2048) (root 10) 2 0) DegreeTwoThreeSpectrum3732.graph fusedMap2048swap=true := by decide +kernel
theorem certified2048swap : Certified (graph core2048) (root 10) 2 0 :=
  of_native_maps core2048 DegreeTwoThreeSpectrum3731.graph DegreeTwoThreeSpectrum3732.graph
    sourceMap2048swap fusedMap2048swap sourceMap2048swap_checked fusedMap2048swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2048
#print axioms sourceMap2048swap_checked
#print axioms fusedMap2048swap_checked
#print axioms certified2048swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
