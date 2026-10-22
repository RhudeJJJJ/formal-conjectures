/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2538 : Family 10 := level10.get ⟨346,by decide⟩
def sourceMap2538 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2538 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2538_checked : acceptsGraphIso
    (source (graph core2538) (root 10) 0 4) DegreeTwoThreeSpectrum5611.graph sourceMap2538=true := by decide +kernel
theorem fusedMap2538_checked : acceptsGraphIso
    (fused (graph core2538) (root 10) 0 4) DegreeTwoThreeSpectrum5612.graph fusedMap2538=true := by decide +kernel
theorem certified2538 : Certified (graph core2538) (root 10) 0 4 :=
  of_native_maps core2538 DegreeTwoThreeSpectrum5611.graph DegreeTwoThreeSpectrum5612.graph
    sourceMap2538 fusedMap2538 sourceMap2538_checked fusedMap2538_checked
    DegreeTwoThreeFiniteComparisons.comparison2538
#print axioms sourceMap2538_checked
#print axioms fusedMap2538_checked
#print axioms certified2538
def sourceMap2538swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2538swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2538swap_checked : acceptsGraphIso
    (source (graph core2538) (root 10) 4 0) DegreeTwoThreeSpectrum5611.graph sourceMap2538swap=true := by decide +kernel
theorem fusedMap2538swap_checked : acceptsGraphIso
    (fused (graph core2538) (root 10) 4 0) DegreeTwoThreeSpectrum5612.graph fusedMap2538swap=true := by decide +kernel
theorem certified2538swap : Certified (graph core2538) (root 10) 4 0 :=
  of_native_maps core2538 DegreeTwoThreeSpectrum5611.graph DegreeTwoThreeSpectrum5612.graph
    sourceMap2538swap fusedMap2538swap sourceMap2538swap_checked fusedMap2538swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2538
#print axioms sourceMap2538swap_checked
#print axioms fusedMap2538swap_checked
#print axioms certified2538swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
