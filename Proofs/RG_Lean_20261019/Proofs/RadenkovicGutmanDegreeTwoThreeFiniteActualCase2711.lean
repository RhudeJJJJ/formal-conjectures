/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2711 : Family 10 := level10.get ⟨850,by decide⟩
def sourceMap2711 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2711 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2711_checked : acceptsGraphIso
    (source (graph core2711) (root 10) 0 4) DegreeTwoThreeSpectrum6895.graph sourceMap2711=true := by decide +kernel
theorem fusedMap2711_checked : acceptsGraphIso
    (fused (graph core2711) (root 10) 0 4) DegreeTwoThreeSpectrum5684.graph fusedMap2711=true := by decide +kernel
theorem certified2711 : Certified (graph core2711) (root 10) 0 4 :=
  of_native_maps core2711 DegreeTwoThreeSpectrum6895.graph DegreeTwoThreeSpectrum5684.graph
    sourceMap2711 fusedMap2711 sourceMap2711_checked fusedMap2711_checked
    DegreeTwoThreeFiniteComparisons.comparison2711
#print axioms sourceMap2711_checked
#print axioms fusedMap2711_checked
#print axioms certified2711
def sourceMap2711swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2711swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2711swap_checked : acceptsGraphIso
    (source (graph core2711) (root 10) 4 0) DegreeTwoThreeSpectrum6895.graph sourceMap2711swap=true := by decide +kernel
theorem fusedMap2711swap_checked : acceptsGraphIso
    (fused (graph core2711) (root 10) 4 0) DegreeTwoThreeSpectrum5684.graph fusedMap2711swap=true := by decide +kernel
theorem certified2711swap : Certified (graph core2711) (root 10) 4 0 :=
  of_native_maps core2711 DegreeTwoThreeSpectrum6895.graph DegreeTwoThreeSpectrum5684.graph
    sourceMap2711swap fusedMap2711swap sourceMap2711swap_checked fusedMap2711swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2711
#print axioms sourceMap2711swap_checked
#print axioms fusedMap2711swap_checked
#print axioms certified2711swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
