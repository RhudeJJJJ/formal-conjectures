/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3495 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3495 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3495 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3495_checked : acceptsGraphIso
    (source (graph core3495) (root 6) 0 6) DegreeTwoThreeSpectrum2708.graph sourceMap3495=true := by decide +kernel
theorem fusedMap3495_checked : acceptsGraphIso
    (fused (graph core3495) (root 6) 0 6) DegreeTwoThreeSpectrum2355.graph fusedMap3495=true := by decide +kernel
theorem certified3495 : Certified (graph core3495) (root 6) 0 6 :=
  of_native_maps core3495 DegreeTwoThreeSpectrum2708.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap3495 fusedMap3495 sourceMap3495_checked fusedMap3495_checked
    DegreeTwoThreeFiniteComparisons.comparison3495
#print axioms sourceMap3495_checked
#print axioms fusedMap3495_checked
#print axioms certified3495
def sourceMap3495swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3495swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3495swap_checked : acceptsGraphIso
    (source (graph core3495) (root 6) 6 0) DegreeTwoThreeSpectrum2708.graph sourceMap3495swap=true := by decide +kernel
theorem fusedMap3495swap_checked : acceptsGraphIso
    (fused (graph core3495) (root 6) 6 0) DegreeTwoThreeSpectrum2355.graph fusedMap3495swap=true := by decide +kernel
theorem certified3495swap : Certified (graph core3495) (root 6) 6 0 :=
  of_native_maps core3495 DegreeTwoThreeSpectrum2708.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap3495swap fusedMap3495swap sourceMap3495swap_checked fusedMap3495swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3495
#print axioms sourceMap3495swap_checked
#print axioms fusedMap3495swap_checked
#print axioms certified3495swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
