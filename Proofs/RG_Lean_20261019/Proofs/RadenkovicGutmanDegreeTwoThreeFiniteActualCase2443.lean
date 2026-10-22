/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2443 : Family 9 := level9.get ⟨651,by decide⟩
def sourceMap2443 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2443 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2443_checked : acceptsGraphIso
    (source (graph core2443) (root 9) 0 4) DegreeTwoThreeSpectrum4815.graph sourceMap2443=true := by decide +kernel
theorem fusedMap2443_checked : acceptsGraphIso
    (fused (graph core2443) (root 9) 0 4) DegreeTwoThreeSpectrum4440.graph fusedMap2443=true := by decide +kernel
theorem certified2443 : Certified (graph core2443) (root 9) 0 4 :=
  of_native_maps core2443 DegreeTwoThreeSpectrum4815.graph DegreeTwoThreeSpectrum4440.graph
    sourceMap2443 fusedMap2443 sourceMap2443_checked fusedMap2443_checked
    DegreeTwoThreeFiniteComparisons.comparison2443
#print axioms sourceMap2443_checked
#print axioms fusedMap2443_checked
#print axioms certified2443
def sourceMap2443swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2443swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2443swap_checked : acceptsGraphIso
    (source (graph core2443) (root 9) 4 0) DegreeTwoThreeSpectrum4815.graph sourceMap2443swap=true := by decide +kernel
theorem fusedMap2443swap_checked : acceptsGraphIso
    (fused (graph core2443) (root 9) 4 0) DegreeTwoThreeSpectrum4440.graph fusedMap2443swap=true := by decide +kernel
theorem certified2443swap : Certified (graph core2443) (root 9) 4 0 :=
  of_native_maps core2443 DegreeTwoThreeSpectrum4815.graph DegreeTwoThreeSpectrum4440.graph
    sourceMap2443swap fusedMap2443swap sourceMap2443swap_checked fusedMap2443swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2443
#print axioms sourceMap2443swap_checked
#print axioms fusedMap2443swap_checked
#print axioms certified2443swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
