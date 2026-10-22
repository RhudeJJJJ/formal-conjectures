/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2741 : Family 10 := level10.get ⟨926,by decide⟩
def sourceMap2741 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2741 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2741_checked : acceptsGraphIso
    (source (graph core2741) (root 10) 0 4) DegreeTwoThreeSpectrum6994.graph sourceMap2741=true := by decide +kernel
theorem fusedMap2741_checked : acceptsGraphIso
    (fused (graph core2741) (root 10) 0 4) DegreeTwoThreeSpectrum5819.graph fusedMap2741=true := by decide +kernel
theorem certified2741 : Certified (graph core2741) (root 10) 0 4 :=
  of_native_maps core2741 DegreeTwoThreeSpectrum6994.graph DegreeTwoThreeSpectrum5819.graph
    sourceMap2741 fusedMap2741 sourceMap2741_checked fusedMap2741_checked
    DegreeTwoThreeFiniteComparisons.comparison2741
#print axioms sourceMap2741_checked
#print axioms fusedMap2741_checked
#print axioms certified2741
def sourceMap2741swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2741swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2741swap_checked : acceptsGraphIso
    (source (graph core2741) (root 10) 4 0) DegreeTwoThreeSpectrum6994.graph sourceMap2741swap=true := by decide +kernel
theorem fusedMap2741swap_checked : acceptsGraphIso
    (fused (graph core2741) (root 10) 4 0) DegreeTwoThreeSpectrum5819.graph fusedMap2741swap=true := by decide +kernel
theorem certified2741swap : Certified (graph core2741) (root 10) 4 0 :=
  of_native_maps core2741 DegreeTwoThreeSpectrum6994.graph DegreeTwoThreeSpectrum5819.graph
    sourceMap2741swap fusedMap2741swap sourceMap2741swap_checked fusedMap2741swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2741
#print axioms sourceMap2741swap_checked
#print axioms fusedMap2741swap_checked
#print axioms certified2741swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
