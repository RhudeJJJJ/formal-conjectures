/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2566 : Family 10 := level10.get ⟨433,by decide⟩
def sourceMap2566 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2566 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2566_checked : acceptsGraphIso
    (source (graph core2566) (root 10) 0 4) DegreeTwoThreeSpectrum5837.graph sourceMap2566=true := by decide +kernel
theorem fusedMap2566_checked : acceptsGraphIso
    (fused (graph core2566) (root 10) 0 4) DegreeTwoThreeSpectrum5838.graph fusedMap2566=true := by decide +kernel
theorem certified2566 : Certified (graph core2566) (root 10) 0 4 :=
  of_native_maps core2566 DegreeTwoThreeSpectrum5837.graph DegreeTwoThreeSpectrum5838.graph
    sourceMap2566 fusedMap2566 sourceMap2566_checked fusedMap2566_checked
    DegreeTwoThreeFiniteComparisons.comparison2566
#print axioms sourceMap2566_checked
#print axioms fusedMap2566_checked
#print axioms certified2566
def sourceMap2566swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2566swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2566swap_checked : acceptsGraphIso
    (source (graph core2566) (root 10) 4 0) DegreeTwoThreeSpectrum5837.graph sourceMap2566swap=true := by decide +kernel
theorem fusedMap2566swap_checked : acceptsGraphIso
    (fused (graph core2566) (root 10) 4 0) DegreeTwoThreeSpectrum5838.graph fusedMap2566swap=true := by decide +kernel
theorem certified2566swap : Certified (graph core2566) (root 10) 4 0 :=
  of_native_maps core2566 DegreeTwoThreeSpectrum5837.graph DegreeTwoThreeSpectrum5838.graph
    sourceMap2566swap fusedMap2566swap sourceMap2566swap_checked fusedMap2566swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2566
#print axioms sourceMap2566swap_checked
#print axioms fusedMap2566swap_checked
#print axioms certified2566swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
