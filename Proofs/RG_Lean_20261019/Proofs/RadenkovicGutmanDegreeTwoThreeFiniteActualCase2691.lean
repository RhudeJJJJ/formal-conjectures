/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2691 : Family 10 := level10.get ⟨796,by decide⟩
def sourceMap2691 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2691 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2691_checked : acceptsGraphIso
    (source (graph core2691) (root 10) 0 4) DegreeTwoThreeSpectrum6745.graph sourceMap2691=true := by decide +kernel
theorem fusedMap2691_checked : acceptsGraphIso
    (fused (graph core2691) (root 10) 0 4) DegreeTwoThreeSpectrum5585.graph fusedMap2691=true := by decide +kernel
theorem certified2691 : Certified (graph core2691) (root 10) 0 4 :=
  of_native_maps core2691 DegreeTwoThreeSpectrum6745.graph DegreeTwoThreeSpectrum5585.graph
    sourceMap2691 fusedMap2691 sourceMap2691_checked fusedMap2691_checked
    DegreeTwoThreeFiniteComparisons.comparison2691
#print axioms sourceMap2691_checked
#print axioms fusedMap2691_checked
#print axioms certified2691
def sourceMap2691swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2691swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2691swap_checked : acceptsGraphIso
    (source (graph core2691) (root 10) 4 0) DegreeTwoThreeSpectrum6745.graph sourceMap2691swap=true := by decide +kernel
theorem fusedMap2691swap_checked : acceptsGraphIso
    (fused (graph core2691) (root 10) 4 0) DegreeTwoThreeSpectrum5585.graph fusedMap2691swap=true := by decide +kernel
theorem certified2691swap : Certified (graph core2691) (root 10) 4 0 :=
  of_native_maps core2691 DegreeTwoThreeSpectrum6745.graph DegreeTwoThreeSpectrum5585.graph
    sourceMap2691swap fusedMap2691swap sourceMap2691swap_checked fusedMap2691swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2691
#print axioms sourceMap2691swap_checked
#print axioms fusedMap2691swap_checked
#print axioms certified2691swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
