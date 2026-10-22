/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2563 : Family 10 := level10.get ⟨422,by decide⟩
def sourceMap2563 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2563 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2563_checked : acceptsGraphIso
    (source (graph core2563) (root 10) 0 4) DegreeTwoThreeSpectrum5807.graph sourceMap2563=true := by decide +kernel
theorem fusedMap2563_checked : acceptsGraphIso
    (fused (graph core2563) (root 10) 0 4) DegreeTwoThreeSpectrum5809.graph fusedMap2563=true := by decide +kernel
theorem certified2563 : Certified (graph core2563) (root 10) 0 4 :=
  of_native_maps core2563 DegreeTwoThreeSpectrum5807.graph DegreeTwoThreeSpectrum5809.graph
    sourceMap2563 fusedMap2563 sourceMap2563_checked fusedMap2563_checked
    DegreeTwoThreeFiniteComparisons.comparison2563
#print axioms sourceMap2563_checked
#print axioms fusedMap2563_checked
#print axioms certified2563
def sourceMap2563swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2563swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2563swap_checked : acceptsGraphIso
    (source (graph core2563) (root 10) 4 0) DegreeTwoThreeSpectrum5807.graph sourceMap2563swap=true := by decide +kernel
theorem fusedMap2563swap_checked : acceptsGraphIso
    (fused (graph core2563) (root 10) 4 0) DegreeTwoThreeSpectrum5809.graph fusedMap2563swap=true := by decide +kernel
theorem certified2563swap : Certified (graph core2563) (root 10) 4 0 :=
  of_native_maps core2563 DegreeTwoThreeSpectrum5807.graph DegreeTwoThreeSpectrum5809.graph
    sourceMap2563swap fusedMap2563swap sourceMap2563swap_checked fusedMap2563swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2563
#print axioms sourceMap2563swap_checked
#print axioms fusedMap2563swap_checked
#print axioms certified2563swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
