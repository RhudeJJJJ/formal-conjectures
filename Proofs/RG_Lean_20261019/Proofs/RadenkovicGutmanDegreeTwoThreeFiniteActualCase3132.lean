/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3132 : Family 7 := level7.get ⟨87,by decide⟩
def sourceMap3132 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3132 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3132_checked : acceptsGraphIso
    (source (graph core3132) (root 7) 0 5) DegreeTwoThreeSpectrum2693.graph sourceMap3132=true := by decide +kernel
theorem fusedMap3132_checked : acceptsGraphIso
    (fused (graph core3132) (root 7) 0 5) DegreeTwoThreeSpectrum2695.graph fusedMap3132=true := by decide +kernel
theorem certified3132 : Certified (graph core3132) (root 7) 0 5 :=
  of_native_maps core3132 DegreeTwoThreeSpectrum2693.graph DegreeTwoThreeSpectrum2695.graph
    sourceMap3132 fusedMap3132 sourceMap3132_checked fusedMap3132_checked
    DegreeTwoThreeFiniteComparisons.comparison3132
#print axioms sourceMap3132_checked
#print axioms fusedMap3132_checked
#print axioms certified3132
def sourceMap3132swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3132swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3132swap_checked : acceptsGraphIso
    (source (graph core3132) (root 7) 5 0) DegreeTwoThreeSpectrum2693.graph sourceMap3132swap=true := by decide +kernel
theorem fusedMap3132swap_checked : acceptsGraphIso
    (fused (graph core3132) (root 7) 5 0) DegreeTwoThreeSpectrum2695.graph fusedMap3132swap=true := by decide +kernel
theorem certified3132swap : Certified (graph core3132) (root 7) 5 0 :=
  of_native_maps core3132 DegreeTwoThreeSpectrum2693.graph DegreeTwoThreeSpectrum2695.graph
    sourceMap3132swap fusedMap3132swap sourceMap3132swap_checked fusedMap3132swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3132
#print axioms sourceMap3132swap_checked
#print axioms fusedMap3132swap_checked
#print axioms certified3132swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
