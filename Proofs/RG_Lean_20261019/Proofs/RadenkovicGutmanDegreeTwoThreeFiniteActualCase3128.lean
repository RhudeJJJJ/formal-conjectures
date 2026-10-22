/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3128 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap3128 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3128 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3128_checked : acceptsGraphIso
    (source (graph core3128) (root 7) 0 5) DegreeTwoThreeSpectrum2563.graph sourceMap3128=true := by decide +kernel
theorem fusedMap3128_checked : acceptsGraphIso
    (fused (graph core3128) (root 7) 0 5) DegreeTwoThreeSpectrum2565.graph fusedMap3128=true := by decide +kernel
theorem certified3128 : Certified (graph core3128) (root 7) 0 5 :=
  of_native_maps core3128 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2565.graph
    sourceMap3128 fusedMap3128 sourceMap3128_checked fusedMap3128_checked
    DegreeTwoThreeFiniteComparisons.comparison3128
#print axioms sourceMap3128_checked
#print axioms fusedMap3128_checked
#print axioms certified3128
def sourceMap3128swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3128swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3128swap_checked : acceptsGraphIso
    (source (graph core3128) (root 7) 5 0) DegreeTwoThreeSpectrum2563.graph sourceMap3128swap=true := by decide +kernel
theorem fusedMap3128swap_checked : acceptsGraphIso
    (fused (graph core3128) (root 7) 5 0) DegreeTwoThreeSpectrum2565.graph fusedMap3128swap=true := by decide +kernel
theorem certified3128swap : Certified (graph core3128) (root 7) 5 0 :=
  of_native_maps core3128 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2565.graph
    sourceMap3128swap fusedMap3128swap sourceMap3128swap_checked fusedMap3128swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3128
#print axioms sourceMap3128swap_checked
#print axioms fusedMap3128swap_checked
#print axioms certified3128swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
