/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2497 : Family 10 := level10.get ⟨194,by decide⟩
def sourceMap2497 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2497 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2497_checked : acceptsGraphIso
    (source (graph core2497) (root 10) 0 4) DegreeTwoThreeSpectrum5157.graph sourceMap2497=true := by decide +kernel
theorem fusedMap2497_checked : acceptsGraphIso
    (fused (graph core2497) (root 10) 0 4) DegreeTwoThreeSpectrum5158.graph fusedMap2497=true := by decide +kernel
theorem certified2497 : Certified (graph core2497) (root 10) 0 4 :=
  of_native_maps core2497 DegreeTwoThreeSpectrum5157.graph DegreeTwoThreeSpectrum5158.graph
    sourceMap2497 fusedMap2497 sourceMap2497_checked fusedMap2497_checked
    DegreeTwoThreeFiniteComparisons.comparison2497
#print axioms sourceMap2497_checked
#print axioms fusedMap2497_checked
#print axioms certified2497
def sourceMap2497swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2497swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2497swap_checked : acceptsGraphIso
    (source (graph core2497) (root 10) 4 0) DegreeTwoThreeSpectrum5157.graph sourceMap2497swap=true := by decide +kernel
theorem fusedMap2497swap_checked : acceptsGraphIso
    (fused (graph core2497) (root 10) 4 0) DegreeTwoThreeSpectrum5158.graph fusedMap2497swap=true := by decide +kernel
theorem certified2497swap : Certified (graph core2497) (root 10) 4 0 :=
  of_native_maps core2497 DegreeTwoThreeSpectrum5157.graph DegreeTwoThreeSpectrum5158.graph
    sourceMap2497swap fusedMap2497swap sourceMap2497swap_checked fusedMap2497swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2497
#print axioms sourceMap2497swap_checked
#print axioms fusedMap2497swap_checked
#print axioms certified2497swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
