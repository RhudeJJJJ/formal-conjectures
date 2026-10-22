/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2470 : Family 10 := level10.get ⟨92,by decide⟩
def sourceMap2470 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2470 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2470_checked : acceptsGraphIso
    (source (graph core2470) (root 10) 0 4) DegreeTwoThreeSpectrum5479.graph sourceMap2470=true := by decide +kernel
theorem fusedMap2470_checked : acceptsGraphIso
    (fused (graph core2470) (root 10) 0 4) DegreeTwoThreeSpectrum5013.graph fusedMap2470=true := by decide +kernel
theorem certified2470 : Certified (graph core2470) (root 10) 0 4 :=
  of_native_maps core2470 DegreeTwoThreeSpectrum5479.graph DegreeTwoThreeSpectrum5013.graph
    sourceMap2470 fusedMap2470 sourceMap2470_checked fusedMap2470_checked
    DegreeTwoThreeFiniteComparisons.comparison2470
#print axioms sourceMap2470_checked
#print axioms fusedMap2470_checked
#print axioms certified2470
def sourceMap2470swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2470swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2470swap_checked : acceptsGraphIso
    (source (graph core2470) (root 10) 4 0) DegreeTwoThreeSpectrum5479.graph sourceMap2470swap=true := by decide +kernel
theorem fusedMap2470swap_checked : acceptsGraphIso
    (fused (graph core2470) (root 10) 4 0) DegreeTwoThreeSpectrum5013.graph fusedMap2470swap=true := by decide +kernel
theorem certified2470swap : Certified (graph core2470) (root 10) 4 0 :=
  of_native_maps core2470 DegreeTwoThreeSpectrum5479.graph DegreeTwoThreeSpectrum5013.graph
    sourceMap2470swap fusedMap2470swap sourceMap2470swap_checked fusedMap2470swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2470
#print axioms sourceMap2470swap_checked
#print axioms fusedMap2470swap_checked
#print axioms certified2470swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
