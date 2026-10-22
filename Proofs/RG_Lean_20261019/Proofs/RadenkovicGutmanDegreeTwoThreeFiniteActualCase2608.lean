/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2608 : Family 10 := level10.get ⟨555,by decide⟩
def sourceMap2608 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2608 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2608_checked : acceptsGraphIso
    (source (graph core2608) (root 10) 0 4) DegreeTwoThreeSpectrum6170.graph sourceMap2608=true := by decide +kernel
theorem fusedMap2608_checked : acceptsGraphIso
    (fused (graph core2608) (root 10) 0 4) DegreeTwoThreeSpectrum5213.graph fusedMap2608=true := by decide +kernel
theorem certified2608 : Certified (graph core2608) (root 10) 0 4 :=
  of_native_maps core2608 DegreeTwoThreeSpectrum6170.graph DegreeTwoThreeSpectrum5213.graph
    sourceMap2608 fusedMap2608 sourceMap2608_checked fusedMap2608_checked
    DegreeTwoThreeFiniteComparisons.comparison2608
#print axioms sourceMap2608_checked
#print axioms fusedMap2608_checked
#print axioms certified2608
def sourceMap2608swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2608swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2608swap_checked : acceptsGraphIso
    (source (graph core2608) (root 10) 4 0) DegreeTwoThreeSpectrum6170.graph sourceMap2608swap=true := by decide +kernel
theorem fusedMap2608swap_checked : acceptsGraphIso
    (fused (graph core2608) (root 10) 4 0) DegreeTwoThreeSpectrum5213.graph fusedMap2608swap=true := by decide +kernel
theorem certified2608swap : Certified (graph core2608) (root 10) 4 0 :=
  of_native_maps core2608 DegreeTwoThreeSpectrum6170.graph DegreeTwoThreeSpectrum5213.graph
    sourceMap2608swap fusedMap2608swap sourceMap2608swap_checked fusedMap2608swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2608
#print axioms sourceMap2608swap_checked
#print axioms fusedMap2608swap_checked
#print axioms certified2608swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
