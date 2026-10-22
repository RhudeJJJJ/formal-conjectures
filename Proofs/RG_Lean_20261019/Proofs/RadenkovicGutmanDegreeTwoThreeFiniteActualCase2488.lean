/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2488 : Family 10 := level10.get ⟨168,by decide⟩
def sourceMap2488 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2488 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2488_checked : acceptsGraphIso
    (source (graph core2488) (root 10) 0 4) DegreeTwoThreeSpectrum5941.graph sourceMap2488=true := by decide +kernel
theorem fusedMap2488_checked : acceptsGraphIso
    (fused (graph core2488) (root 10) 0 4) DegreeTwoThreeSpectrum5110.graph fusedMap2488=true := by decide +kernel
theorem certified2488 : Certified (graph core2488) (root 10) 0 4 :=
  of_native_maps core2488 DegreeTwoThreeSpectrum5941.graph DegreeTwoThreeSpectrum5110.graph
    sourceMap2488 fusedMap2488 sourceMap2488_checked fusedMap2488_checked
    DegreeTwoThreeFiniteComparisons.comparison2488
#print axioms sourceMap2488_checked
#print axioms fusedMap2488_checked
#print axioms certified2488
def sourceMap2488swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2488swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2488swap_checked : acceptsGraphIso
    (source (graph core2488) (root 10) 4 0) DegreeTwoThreeSpectrum5941.graph sourceMap2488swap=true := by decide +kernel
theorem fusedMap2488swap_checked : acceptsGraphIso
    (fused (graph core2488) (root 10) 4 0) DegreeTwoThreeSpectrum5110.graph fusedMap2488swap=true := by decide +kernel
theorem certified2488swap : Certified (graph core2488) (root 10) 4 0 :=
  of_native_maps core2488 DegreeTwoThreeSpectrum5941.graph DegreeTwoThreeSpectrum5110.graph
    sourceMap2488swap fusedMap2488swap sourceMap2488swap_checked fusedMap2488swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2488
#print axioms sourceMap2488swap_checked
#print axioms fusedMap2488swap_checked
#print axioms certified2488swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
