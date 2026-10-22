/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1576 : Family 10 := level10.get ⟨531,by decide⟩
def sourceMap1576 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1576 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1576_checked : acceptsGraphIso
    (source (graph core1576) (root 10) 0 2) DegreeTwoThreeSpectrum3109.graph sourceMap1576=true := by decide +kernel
theorem fusedMap1576_checked : acceptsGraphIso
    (fused (graph core1576) (root 10) 0 2) DegreeTwoThreeSpectrum2468.graph fusedMap1576=true := by decide +kernel
theorem certified1576 : Certified (graph core1576) (root 10) 0 2 :=
  of_native_maps core1576 DegreeTwoThreeSpectrum3109.graph DegreeTwoThreeSpectrum2468.graph
    sourceMap1576 fusedMap1576 sourceMap1576_checked fusedMap1576_checked
    DegreeTwoThreeFiniteComparisons.comparison1576
#print axioms sourceMap1576_checked
#print axioms fusedMap1576_checked
#print axioms certified1576
def sourceMap1576swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1576swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1576swap_checked : acceptsGraphIso
    (source (graph core1576) (root 10) 2 0) DegreeTwoThreeSpectrum3109.graph sourceMap1576swap=true := by decide +kernel
theorem fusedMap1576swap_checked : acceptsGraphIso
    (fused (graph core1576) (root 10) 2 0) DegreeTwoThreeSpectrum2468.graph fusedMap1576swap=true := by decide +kernel
theorem certified1576swap : Certified (graph core1576) (root 10) 2 0 :=
  of_native_maps core1576 DegreeTwoThreeSpectrum3109.graph DegreeTwoThreeSpectrum2468.graph
    sourceMap1576swap fusedMap1576swap sourceMap1576swap_checked fusedMap1576swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1576
#print axioms sourceMap1576swap_checked
#print axioms fusedMap1576swap_checked
#print axioms certified1576swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
