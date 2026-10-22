/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2628 : Family 10 := level10.get ⟨619,by decide⟩
def sourceMap2628 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2628 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2628_checked : acceptsGraphIso
    (source (graph core2628) (root 10) 0 4) DegreeTwoThreeSpectrum6355.graph sourceMap2628=true := by decide +kernel
theorem fusedMap2628_checked : acceptsGraphIso
    (fused (graph core2628) (root 10) 0 4) DegreeTwoThreeSpectrum5309.graph fusedMap2628=true := by decide +kernel
theorem certified2628 : Certified (graph core2628) (root 10) 0 4 :=
  of_native_maps core2628 DegreeTwoThreeSpectrum6355.graph DegreeTwoThreeSpectrum5309.graph
    sourceMap2628 fusedMap2628 sourceMap2628_checked fusedMap2628_checked
    DegreeTwoThreeFiniteComparisons.comparison2628
#print axioms sourceMap2628_checked
#print axioms fusedMap2628_checked
#print axioms certified2628
def sourceMap2628swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2628swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2628swap_checked : acceptsGraphIso
    (source (graph core2628) (root 10) 4 0) DegreeTwoThreeSpectrum6355.graph sourceMap2628swap=true := by decide +kernel
theorem fusedMap2628swap_checked : acceptsGraphIso
    (fused (graph core2628) (root 10) 4 0) DegreeTwoThreeSpectrum5309.graph fusedMap2628swap=true := by decide +kernel
theorem certified2628swap : Certified (graph core2628) (root 10) 4 0 :=
  of_native_maps core2628 DegreeTwoThreeSpectrum6355.graph DegreeTwoThreeSpectrum5309.graph
    sourceMap2628swap fusedMap2628swap sourceMap2628swap_checked fusedMap2628swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2628
#print axioms sourceMap2628swap_checked
#print axioms fusedMap2628swap_checked
#print axioms certified2628swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
