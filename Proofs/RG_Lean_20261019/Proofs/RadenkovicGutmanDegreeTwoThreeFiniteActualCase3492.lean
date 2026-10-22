/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3492 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap3492 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3492 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3492_checked : acceptsGraphIso
    (source (graph core3492) (root 6) 0 6) DegreeTwoThreeSpectrum2538.graph sourceMap3492=true := by decide +kernel
theorem fusedMap3492_checked : acceptsGraphIso
    (fused (graph core3492) (root 6) 0 6) DegreeTwoThreeSpectrum2323.graph fusedMap3492=true := by decide +kernel
theorem certified3492 : Certified (graph core3492) (root 6) 0 6 :=
  of_native_maps core3492 DegreeTwoThreeSpectrum2538.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap3492 fusedMap3492 sourceMap3492_checked fusedMap3492_checked
    DegreeTwoThreeFiniteComparisons.comparison3492
#print axioms sourceMap3492_checked
#print axioms fusedMap3492_checked
#print axioms certified3492
def sourceMap3492swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3492swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3492swap_checked : acceptsGraphIso
    (source (graph core3492) (root 6) 6 0) DegreeTwoThreeSpectrum2538.graph sourceMap3492swap=true := by decide +kernel
theorem fusedMap3492swap_checked : acceptsGraphIso
    (fused (graph core3492) (root 6) 6 0) DegreeTwoThreeSpectrum2323.graph fusedMap3492swap=true := by decide +kernel
theorem certified3492swap : Certified (graph core3492) (root 6) 6 0 :=
  of_native_maps core3492 DegreeTwoThreeSpectrum2538.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap3492swap fusedMap3492swap sourceMap3492swap_checked fusedMap3492swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3492
#print axioms sourceMap3492swap_checked
#print axioms fusedMap3492swap_checked
#print axioms certified3492swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
