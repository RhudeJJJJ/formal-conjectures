/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2501 : Family 10 := level10.get ⟨212,by decide⟩
def sourceMap2501 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2501 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2501_checked : acceptsGraphIso
    (source (graph core2501) (root 10) 0 4) DegreeTwoThreeSpectrum5218.graph sourceMap2501=true := by decide +kernel
theorem fusedMap2501_checked : acceptsGraphIso
    (fused (graph core2501) (root 10) 0 4) DegreeTwoThreeSpectrum5219.graph fusedMap2501=true := by decide +kernel
theorem certified2501 : Certified (graph core2501) (root 10) 0 4 :=
  of_native_maps core2501 DegreeTwoThreeSpectrum5218.graph DegreeTwoThreeSpectrum5219.graph
    sourceMap2501 fusedMap2501 sourceMap2501_checked fusedMap2501_checked
    DegreeTwoThreeFiniteComparisons.comparison2501
#print axioms sourceMap2501_checked
#print axioms fusedMap2501_checked
#print axioms certified2501
def sourceMap2501swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2501swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2501swap_checked : acceptsGraphIso
    (source (graph core2501) (root 10) 4 0) DegreeTwoThreeSpectrum5218.graph sourceMap2501swap=true := by decide +kernel
theorem fusedMap2501swap_checked : acceptsGraphIso
    (fused (graph core2501) (root 10) 4 0) DegreeTwoThreeSpectrum5219.graph fusedMap2501swap=true := by decide +kernel
theorem certified2501swap : Certified (graph core2501) (root 10) 4 0 :=
  of_native_maps core2501 DegreeTwoThreeSpectrum5218.graph DegreeTwoThreeSpectrum5219.graph
    sourceMap2501swap fusedMap2501swap sourceMap2501swap_checked fusedMap2501swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2501
#print axioms sourceMap2501swap_checked
#print axioms fusedMap2501swap_checked
#print axioms certified2501swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
