/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3110 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap3110 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3110 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3110_checked : acceptsGraphIso
    (source (graph core3110) (root 7) 0 5) DegreeTwoThreeSpectrum2549.graph sourceMap3110=true := by decide +kernel
theorem fusedMap3110_checked : acceptsGraphIso
    (fused (graph core3110) (root 7) 0 5) DegreeTwoThreeSpectrum2324.graph fusedMap3110=true := by decide +kernel
theorem certified3110 : Certified (graph core3110) (root 7) 0 5 :=
  of_native_maps core3110 DegreeTwoThreeSpectrum2549.graph DegreeTwoThreeSpectrum2324.graph
    sourceMap3110 fusedMap3110 sourceMap3110_checked fusedMap3110_checked
    DegreeTwoThreeFiniteComparisons.comparison3110
#print axioms sourceMap3110_checked
#print axioms fusedMap3110_checked
#print axioms certified3110
def sourceMap3110swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3110swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3110swap_checked : acceptsGraphIso
    (source (graph core3110) (root 7) 5 0) DegreeTwoThreeSpectrum2549.graph sourceMap3110swap=true := by decide +kernel
theorem fusedMap3110swap_checked : acceptsGraphIso
    (fused (graph core3110) (root 7) 5 0) DegreeTwoThreeSpectrum2324.graph fusedMap3110swap=true := by decide +kernel
theorem certified3110swap : Certified (graph core3110) (root 7) 5 0 :=
  of_native_maps core3110 DegreeTwoThreeSpectrum2549.graph DegreeTwoThreeSpectrum2324.graph
    sourceMap3110swap fusedMap3110swap sourceMap3110swap_checked fusedMap3110swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3110
#print axioms sourceMap3110swap_checked
#print axioms fusedMap3110swap_checked
#print axioms certified3110swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
