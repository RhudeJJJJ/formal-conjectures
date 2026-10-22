/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2520 : Family 10 := level10.get ⟨278,by decide⟩
def sourceMap2520 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2520 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2520_checked : acceptsGraphIso
    (source (graph core2520) (root 10) 0 4) DegreeTwoThreeSpectrum5409.graph sourceMap2520=true := by decide +kernel
theorem fusedMap2520_checked : acceptsGraphIso
    (fused (graph core2520) (root 10) 0 4) DegreeTwoThreeSpectrum5411.graph fusedMap2520=true := by decide +kernel
theorem certified2520 : Certified (graph core2520) (root 10) 0 4 :=
  of_native_maps core2520 DegreeTwoThreeSpectrum5409.graph DegreeTwoThreeSpectrum5411.graph
    sourceMap2520 fusedMap2520 sourceMap2520_checked fusedMap2520_checked
    DegreeTwoThreeFiniteComparisons.comparison2520
#print axioms sourceMap2520_checked
#print axioms fusedMap2520_checked
#print axioms certified2520
def sourceMap2520swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2520swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2520swap_checked : acceptsGraphIso
    (source (graph core2520) (root 10) 4 0) DegreeTwoThreeSpectrum5409.graph sourceMap2520swap=true := by decide +kernel
theorem fusedMap2520swap_checked : acceptsGraphIso
    (fused (graph core2520) (root 10) 4 0) DegreeTwoThreeSpectrum5411.graph fusedMap2520swap=true := by decide +kernel
theorem certified2520swap : Certified (graph core2520) (root 10) 4 0 :=
  of_native_maps core2520 DegreeTwoThreeSpectrum5409.graph DegreeTwoThreeSpectrum5411.graph
    sourceMap2520swap fusedMap2520swap sourceMap2520swap_checked fusedMap2520swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2520
#print axioms sourceMap2520swap_checked
#print axioms fusedMap2520swap_checked
#print axioms certified2520swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
