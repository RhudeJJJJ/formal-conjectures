/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2503 : Family 10 := level10.get ⟨220,by decide⟩
def sourceMap2503 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2503 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2503_checked : acceptsGraphIso
    (source (graph core2503) (root 10) 0 4) DegreeTwoThreeSpectrum5245.graph sourceMap2503=true := by decide +kernel
theorem fusedMap2503_checked : acceptsGraphIso
    (fused (graph core2503) (root 10) 0 4) DegreeTwoThreeSpectrum5246.graph fusedMap2503=true := by decide +kernel
theorem certified2503 : Certified (graph core2503) (root 10) 0 4 :=
  of_native_maps core2503 DegreeTwoThreeSpectrum5245.graph DegreeTwoThreeSpectrum5246.graph
    sourceMap2503 fusedMap2503 sourceMap2503_checked fusedMap2503_checked
    DegreeTwoThreeFiniteComparisons.comparison2503
#print axioms sourceMap2503_checked
#print axioms fusedMap2503_checked
#print axioms certified2503
def sourceMap2503swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2503swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2503swap_checked : acceptsGraphIso
    (source (graph core2503) (root 10) 4 0) DegreeTwoThreeSpectrum5245.graph sourceMap2503swap=true := by decide +kernel
theorem fusedMap2503swap_checked : acceptsGraphIso
    (fused (graph core2503) (root 10) 4 0) DegreeTwoThreeSpectrum5246.graph fusedMap2503swap=true := by decide +kernel
theorem certified2503swap : Certified (graph core2503) (root 10) 4 0 :=
  of_native_maps core2503 DegreeTwoThreeSpectrum5245.graph DegreeTwoThreeSpectrum5246.graph
    sourceMap2503swap fusedMap2503swap sourceMap2503swap_checked fusedMap2503swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2503
#print axioms sourceMap2503swap_checked
#print axioms fusedMap2503swap_checked
#print axioms certified2503swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
