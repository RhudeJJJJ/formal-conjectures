/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3103 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap3103 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 7 0 5 v)
def fusedMap3103 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3103_checked : acceptsGraphIso
    (source (graph core3103) (root 7) 0 5) DegreeTwoThreeSpectrum2436.graph sourceMap3103=true := by decide +kernel
theorem fusedMap3103_checked : acceptsGraphIso
    (fused (graph core3103) (root 7) 0 5) DegreeTwoThreeSpectrum2314.graph fusedMap3103=true := by decide +kernel
theorem certified3103 : Certified (graph core3103) (root 7) 0 5 :=
  of_native_maps core3103 DegreeTwoThreeSpectrum2436.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap3103 fusedMap3103 sourceMap3103_checked fusedMap3103_checked
    DegreeTwoThreeFiniteComparisons.comparison3103
#print axioms sourceMap3103_checked
#print axioms fusedMap3103_checked
#print axioms certified3103
def sourceMap3103swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12,14] (sourceLabel 7 5 0 v)
def fusedMap3103swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3103swap_checked : acceptsGraphIso
    (source (graph core3103) (root 7) 5 0) DegreeTwoThreeSpectrum2436.graph sourceMap3103swap=true := by decide +kernel
theorem fusedMap3103swap_checked : acceptsGraphIso
    (fused (graph core3103) (root 7) 5 0) DegreeTwoThreeSpectrum2314.graph fusedMap3103swap=true := by decide +kernel
theorem certified3103swap : Certified (graph core3103) (root 7) 5 0 :=
  of_native_maps core3103 DegreeTwoThreeSpectrum2436.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap3103swap fusedMap3103swap sourceMap3103swap_checked fusedMap3103swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3103
#print axioms sourceMap3103swap_checked
#print axioms fusedMap3103swap_checked
#print axioms certified3103swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
