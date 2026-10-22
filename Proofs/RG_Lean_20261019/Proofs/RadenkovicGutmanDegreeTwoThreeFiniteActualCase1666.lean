/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1666 : Family 10 := level10.get ⟨793,by decide⟩
def sourceMap1666 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1666 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1666_checked : acceptsGraphIso
    (source (graph core1666) (root 10) 0 2) DegreeTwoThreeSpectrum3582.graph sourceMap1666=true := by decide +kernel
theorem fusedMap1666_checked : acceptsGraphIso
    (fused (graph core1666) (root 10) 0 2) DegreeTwoThreeSpectrum2758.graph fusedMap1666=true := by decide +kernel
theorem certified1666 : Certified (graph core1666) (root 10) 0 2 :=
  of_native_maps core1666 DegreeTwoThreeSpectrum3582.graph DegreeTwoThreeSpectrum2758.graph
    sourceMap1666 fusedMap1666 sourceMap1666_checked fusedMap1666_checked
    DegreeTwoThreeFiniteComparisons.comparison1666
#print axioms sourceMap1666_checked
#print axioms fusedMap1666_checked
#print axioms certified1666
def sourceMap1666swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1666swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1666swap_checked : acceptsGraphIso
    (source (graph core1666) (root 10) 2 0) DegreeTwoThreeSpectrum3582.graph sourceMap1666swap=true := by decide +kernel
theorem fusedMap1666swap_checked : acceptsGraphIso
    (fused (graph core1666) (root 10) 2 0) DegreeTwoThreeSpectrum2758.graph fusedMap1666swap=true := by decide +kernel
theorem certified1666swap : Certified (graph core1666) (root 10) 2 0 :=
  of_native_maps core1666 DegreeTwoThreeSpectrum3582.graph DegreeTwoThreeSpectrum2758.graph
    sourceMap1666swap fusedMap1666swap sourceMap1666swap_checked fusedMap1666swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1666
#print axioms sourceMap1666swap_checked
#print axioms fusedMap1666swap_checked
#print axioms certified1666swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
