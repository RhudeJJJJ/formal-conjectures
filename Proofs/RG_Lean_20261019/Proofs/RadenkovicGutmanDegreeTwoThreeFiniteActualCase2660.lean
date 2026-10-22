/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2660 : Family 10 := level10.get ⟨710,by decide⟩
def sourceMap2660 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2660 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2660_checked : acceptsGraphIso
    (source (graph core2660) (root 10) 0 4) DegreeTwoThreeSpectrum6557.graph sourceMap2660=true := by decide +kernel
theorem fusedMap2660_checked : acceptsGraphIso
    (fused (graph core2660) (root 10) 0 4) DegreeTwoThreeSpectrum5452.graph fusedMap2660=true := by decide +kernel
theorem certified2660 : Certified (graph core2660) (root 10) 0 4 :=
  of_native_maps core2660 DegreeTwoThreeSpectrum6557.graph DegreeTwoThreeSpectrum5452.graph
    sourceMap2660 fusedMap2660 sourceMap2660_checked fusedMap2660_checked
    DegreeTwoThreeFiniteComparisons.comparison2660
#print axioms sourceMap2660_checked
#print axioms fusedMap2660_checked
#print axioms certified2660
def sourceMap2660swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2660swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2660swap_checked : acceptsGraphIso
    (source (graph core2660) (root 10) 4 0) DegreeTwoThreeSpectrum6557.graph sourceMap2660swap=true := by decide +kernel
theorem fusedMap2660swap_checked : acceptsGraphIso
    (fused (graph core2660) (root 10) 4 0) DegreeTwoThreeSpectrum5452.graph fusedMap2660swap=true := by decide +kernel
theorem certified2660swap : Certified (graph core2660) (root 10) 4 0 :=
  of_native_maps core2660 DegreeTwoThreeSpectrum6557.graph DegreeTwoThreeSpectrum5452.graph
    sourceMap2660swap fusedMap2660swap sourceMap2660swap_checked fusedMap2660swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2660
#print axioms sourceMap2660swap_checked
#print axioms fusedMap2660swap_checked
#print axioms certified2660swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
