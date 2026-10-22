/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2335 : Family 9 := level9.get ⟨389,by decide⟩
def sourceMap2335 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2335 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2335_checked : acceptsGraphIso
    (source (graph core2335) (root 9) 0 4) DegreeTwoThreeSpectrum4337.graph sourceMap2335=true := by decide +kernel
theorem fusedMap2335_checked : acceptsGraphIso
    (fused (graph core2335) (root 9) 0 4) DegreeTwoThreeSpectrum4338.graph fusedMap2335=true := by decide +kernel
theorem certified2335 : Certified (graph core2335) (root 9) 0 4 :=
  of_native_maps core2335 DegreeTwoThreeSpectrum4337.graph DegreeTwoThreeSpectrum4338.graph
    sourceMap2335 fusedMap2335 sourceMap2335_checked fusedMap2335_checked
    DegreeTwoThreeFiniteComparisons.comparison2335
#print axioms sourceMap2335_checked
#print axioms fusedMap2335_checked
#print axioms certified2335
def sourceMap2335swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2335swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2335swap_checked : acceptsGraphIso
    (source (graph core2335) (root 9) 4 0) DegreeTwoThreeSpectrum4337.graph sourceMap2335swap=true := by decide +kernel
theorem fusedMap2335swap_checked : acceptsGraphIso
    (fused (graph core2335) (root 9) 4 0) DegreeTwoThreeSpectrum4338.graph fusedMap2335swap=true := by decide +kernel
theorem certified2335swap : Certified (graph core2335) (root 9) 4 0 :=
  of_native_maps core2335 DegreeTwoThreeSpectrum4337.graph DegreeTwoThreeSpectrum4338.graph
    sourceMap2335swap fusedMap2335swap sourceMap2335swap_checked fusedMap2335swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2335
#print axioms sourceMap2335swap_checked
#print axioms fusedMap2335swap_checked
#print axioms certified2335swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
