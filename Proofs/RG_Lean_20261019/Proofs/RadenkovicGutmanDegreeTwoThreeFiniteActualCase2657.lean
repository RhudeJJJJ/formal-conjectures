/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2657 : Family 10 := level10.get ⟨698,by decide⟩
def sourceMap2657 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2657 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2657_checked : acceptsGraphIso
    (source (graph core2657) (root 10) 0 4) DegreeTwoThreeSpectrum6525.graph sourceMap2657=true := by decide +kernel
theorem fusedMap2657_checked : acceptsGraphIso
    (fused (graph core2657) (root 10) 0 4) DegreeTwoThreeSpectrum5436.graph fusedMap2657=true := by decide +kernel
theorem certified2657 : Certified (graph core2657) (root 10) 0 4 :=
  of_native_maps core2657 DegreeTwoThreeSpectrum6525.graph DegreeTwoThreeSpectrum5436.graph
    sourceMap2657 fusedMap2657 sourceMap2657_checked fusedMap2657_checked
    DegreeTwoThreeFiniteComparisons.comparison2657
#print axioms sourceMap2657_checked
#print axioms fusedMap2657_checked
#print axioms certified2657
def sourceMap2657swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2657swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2657swap_checked : acceptsGraphIso
    (source (graph core2657) (root 10) 4 0) DegreeTwoThreeSpectrum6525.graph sourceMap2657swap=true := by decide +kernel
theorem fusedMap2657swap_checked : acceptsGraphIso
    (fused (graph core2657) (root 10) 4 0) DegreeTwoThreeSpectrum5436.graph fusedMap2657swap=true := by decide +kernel
theorem certified2657swap : Certified (graph core2657) (root 10) 4 0 :=
  of_native_maps core2657 DegreeTwoThreeSpectrum6525.graph DegreeTwoThreeSpectrum5436.graph
    sourceMap2657swap fusedMap2657swap sourceMap2657swap_checked fusedMap2657swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2657
#print axioms sourceMap2657swap_checked
#print axioms fusedMap2657swap_checked
#print axioms certified2657swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
