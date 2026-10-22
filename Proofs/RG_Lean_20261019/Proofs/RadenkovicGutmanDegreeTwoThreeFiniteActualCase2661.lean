/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2661 : Family 10 := level10.get ⟨711,by decide⟩
def sourceMap2661 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2661 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2661_checked : acceptsGraphIso
    (source (graph core2661) (root 10) 0 4) DegreeTwoThreeSpectrum6559.graph sourceMap2661=true := by decide +kernel
theorem fusedMap2661_checked : acceptsGraphIso
    (fused (graph core2661) (root 10) 0 4) DegreeTwoThreeSpectrum5454.graph fusedMap2661=true := by decide +kernel
theorem certified2661 : Certified (graph core2661) (root 10) 0 4 :=
  of_native_maps core2661 DegreeTwoThreeSpectrum6559.graph DegreeTwoThreeSpectrum5454.graph
    sourceMap2661 fusedMap2661 sourceMap2661_checked fusedMap2661_checked
    DegreeTwoThreeFiniteComparisons.comparison2661
#print axioms sourceMap2661_checked
#print axioms fusedMap2661_checked
#print axioms certified2661
def sourceMap2661swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2661swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2661swap_checked : acceptsGraphIso
    (source (graph core2661) (root 10) 4 0) DegreeTwoThreeSpectrum6559.graph sourceMap2661swap=true := by decide +kernel
theorem fusedMap2661swap_checked : acceptsGraphIso
    (fused (graph core2661) (root 10) 4 0) DegreeTwoThreeSpectrum5454.graph fusedMap2661swap=true := by decide +kernel
theorem certified2661swap : Certified (graph core2661) (root 10) 4 0 :=
  of_native_maps core2661 DegreeTwoThreeSpectrum6559.graph DegreeTwoThreeSpectrum5454.graph
    sourceMap2661swap fusedMap2661swap sourceMap2661swap_checked fusedMap2661swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2661
#print axioms sourceMap2661swap_checked
#print axioms fusedMap2661swap_checked
#print axioms certified2661swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
