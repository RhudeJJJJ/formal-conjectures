/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2736 : Family 10 := level10.get ⟨913,by decide⟩
def sourceMap2736 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2736 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2736_checked : acceptsGraphIso
    (source (graph core2736) (root 10) 0 4) DegreeTwoThreeSpectrum6986.graph sourceMap2736=true := by decide +kernel
theorem fusedMap2736_checked : acceptsGraphIso
    (fused (graph core2736) (root 10) 0 4) DegreeTwoThreeSpectrum5784.graph fusedMap2736=true := by decide +kernel
theorem certified2736 : Certified (graph core2736) (root 10) 0 4 :=
  of_native_maps core2736 DegreeTwoThreeSpectrum6986.graph DegreeTwoThreeSpectrum5784.graph
    sourceMap2736 fusedMap2736 sourceMap2736_checked fusedMap2736_checked
    DegreeTwoThreeFiniteComparisons.comparison2736
#print axioms sourceMap2736_checked
#print axioms fusedMap2736_checked
#print axioms certified2736
def sourceMap2736swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2736swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2736swap_checked : acceptsGraphIso
    (source (graph core2736) (root 10) 4 0) DegreeTwoThreeSpectrum6986.graph sourceMap2736swap=true := by decide +kernel
theorem fusedMap2736swap_checked : acceptsGraphIso
    (fused (graph core2736) (root 10) 4 0) DegreeTwoThreeSpectrum5784.graph fusedMap2736swap=true := by decide +kernel
theorem certified2736swap : Certified (graph core2736) (root 10) 4 0 :=
  of_native_maps core2736 DegreeTwoThreeSpectrum6986.graph DegreeTwoThreeSpectrum5784.graph
    sourceMap2736swap fusedMap2736swap sourceMap2736swap_checked fusedMap2736swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2736
#print axioms sourceMap2736swap_checked
#print axioms fusedMap2736swap_checked
#print axioms certified2736swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
