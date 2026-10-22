/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2590 : Family 10 := level10.get ⟨492,by decide⟩
def sourceMap2590 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,10,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2590 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 0 4 v)
theorem sourceMap2590_checked : acceptsGraphIso
    (source (graph core2590) (root 10) 0 4) DegreeTwoThreeSpectrum5929.graph sourceMap2590=true := by decide +kernel
theorem fusedMap2590_checked : acceptsGraphIso
    (fused (graph core2590) (root 10) 0 4) DegreeTwoThreeSpectrum5957.graph fusedMap2590=true := by decide +kernel
theorem certified2590 : Certified (graph core2590) (root 10) 0 4 :=
  of_native_maps core2590 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum5957.graph
    sourceMap2590 fusedMap2590 sourceMap2590_checked fusedMap2590_checked
    DegreeTwoThreeFiniteComparisons.comparison2590
#print axioms sourceMap2590_checked
#print axioms fusedMap2590_checked
#print axioms certified2590
def sourceMap2590swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5,10] (sourceLabel 10 4 0 v)
def fusedMap2590swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 4 0 v)
theorem sourceMap2590swap_checked : acceptsGraphIso
    (source (graph core2590) (root 10) 4 0) DegreeTwoThreeSpectrum5929.graph sourceMap2590swap=true := by decide +kernel
theorem fusedMap2590swap_checked : acceptsGraphIso
    (fused (graph core2590) (root 10) 4 0) DegreeTwoThreeSpectrum5957.graph fusedMap2590swap=true := by decide +kernel
theorem certified2590swap : Certified (graph core2590) (root 10) 4 0 :=
  of_native_maps core2590 DegreeTwoThreeSpectrum5929.graph DegreeTwoThreeSpectrum5957.graph
    sourceMap2590swap fusedMap2590swap sourceMap2590swap_checked fusedMap2590swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2590
#print axioms sourceMap2590swap_checked
#print axioms fusedMap2590swap_checked
#print axioms certified2590swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
