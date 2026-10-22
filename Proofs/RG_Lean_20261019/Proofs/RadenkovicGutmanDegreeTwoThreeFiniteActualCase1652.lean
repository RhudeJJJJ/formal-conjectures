/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1652 : Family 10 := level10.get ⟨754,by decide⟩
def sourceMap1652 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1652 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1652_checked : acceptsGraphIso
    (source (graph core1652) (root 10) 0 2) DegreeTwoThreeSpectrum3521.graph sourceMap1652=true := by decide +kernel
theorem fusedMap1652_checked : acceptsGraphIso
    (fused (graph core1652) (root 10) 0 2) DegreeTwoThreeSpectrum2716.graph fusedMap1652=true := by decide +kernel
theorem certified1652 : Certified (graph core1652) (root 10) 0 2 :=
  of_native_maps core1652 DegreeTwoThreeSpectrum3521.graph DegreeTwoThreeSpectrum2716.graph
    sourceMap1652 fusedMap1652 sourceMap1652_checked fusedMap1652_checked
    DegreeTwoThreeFiniteComparisons.comparison1652
#print axioms sourceMap1652_checked
#print axioms fusedMap1652_checked
#print axioms certified1652
def sourceMap1652swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1652swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1652swap_checked : acceptsGraphIso
    (source (graph core1652) (root 10) 2 0) DegreeTwoThreeSpectrum3521.graph sourceMap1652swap=true := by decide +kernel
theorem fusedMap1652swap_checked : acceptsGraphIso
    (fused (graph core1652) (root 10) 2 0) DegreeTwoThreeSpectrum2716.graph fusedMap1652swap=true := by decide +kernel
theorem certified1652swap : Certified (graph core1652) (root 10) 2 0 :=
  of_native_maps core1652 DegreeTwoThreeSpectrum3521.graph DegreeTwoThreeSpectrum2716.graph
    sourceMap1652swap fusedMap1652swap sourceMap1652swap_checked fusedMap1652swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1652
#print axioms sourceMap1652swap_checked
#print axioms fusedMap1652swap_checked
#print axioms certified1652swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
