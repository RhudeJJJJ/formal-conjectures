/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2580 : Family 10 := level10.get ⟨474,by decide⟩
def sourceMap2580 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2580 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2580_checked : acceptsGraphIso
    (source (graph core2580) (root 10) 0 4) DegreeTwoThreeSpectrum5934.graph sourceMap2580=true := by decide +kernel
theorem fusedMap2580_checked : acceptsGraphIso
    (fused (graph core2580) (root 10) 0 4) DegreeTwoThreeSpectrum5935.graph fusedMap2580=true := by decide +kernel
theorem certified2580 : Certified (graph core2580) (root 10) 0 4 :=
  of_native_maps core2580 DegreeTwoThreeSpectrum5934.graph DegreeTwoThreeSpectrum5935.graph
    sourceMap2580 fusedMap2580 sourceMap2580_checked fusedMap2580_checked
    DegreeTwoThreeFiniteComparisons.comparison2580
#print axioms sourceMap2580_checked
#print axioms fusedMap2580_checked
#print axioms certified2580
def sourceMap2580swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2580swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2580swap_checked : acceptsGraphIso
    (source (graph core2580) (root 10) 4 0) DegreeTwoThreeSpectrum5934.graph sourceMap2580swap=true := by decide +kernel
theorem fusedMap2580swap_checked : acceptsGraphIso
    (fused (graph core2580) (root 10) 4 0) DegreeTwoThreeSpectrum5935.graph fusedMap2580swap=true := by decide +kernel
theorem certified2580swap : Certified (graph core2580) (root 10) 4 0 :=
  of_native_maps core2580 DegreeTwoThreeSpectrum5934.graph DegreeTwoThreeSpectrum5935.graph
    sourceMap2580swap fusedMap2580swap sourceMap2580swap_checked fusedMap2580swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2580
#print axioms sourceMap2580swap_checked
#print axioms fusedMap2580swap_checked
#print axioms certified2580swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
