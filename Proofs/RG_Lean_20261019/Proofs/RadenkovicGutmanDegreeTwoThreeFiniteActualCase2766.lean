/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2766 : Family 10 := level10.get ⟨980,by decide⟩
def sourceMap2766 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2766 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2766_checked : acceptsGraphIso
    (source (graph core2766) (root 10) 0 4) DegreeTwoThreeSpectrum7046.graph sourceMap2766=true := by decide +kernel
theorem fusedMap2766_checked : acceptsGraphIso
    (fused (graph core2766) (root 10) 0 4) DegreeTwoThreeSpectrum5915.graph fusedMap2766=true := by decide +kernel
theorem certified2766 : Certified (graph core2766) (root 10) 0 4 :=
  of_native_maps core2766 DegreeTwoThreeSpectrum7046.graph DegreeTwoThreeSpectrum5915.graph
    sourceMap2766 fusedMap2766 sourceMap2766_checked fusedMap2766_checked
    DegreeTwoThreeFiniteComparisons.comparison2766
#print axioms sourceMap2766_checked
#print axioms fusedMap2766_checked
#print axioms certified2766
def sourceMap2766swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2766swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2766swap_checked : acceptsGraphIso
    (source (graph core2766) (root 10) 4 0) DegreeTwoThreeSpectrum7046.graph sourceMap2766swap=true := by decide +kernel
theorem fusedMap2766swap_checked : acceptsGraphIso
    (fused (graph core2766) (root 10) 4 0) DegreeTwoThreeSpectrum5915.graph fusedMap2766swap=true := by decide +kernel
theorem certified2766swap : Certified (graph core2766) (root 10) 4 0 :=
  of_native_maps core2766 DegreeTwoThreeSpectrum7046.graph DegreeTwoThreeSpectrum5915.graph
    sourceMap2766swap fusedMap2766swap sourceMap2766swap_checked fusedMap2766swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2766
#print axioms sourceMap2766swap_checked
#print axioms fusedMap2766swap_checked
#print axioms certified2766swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
