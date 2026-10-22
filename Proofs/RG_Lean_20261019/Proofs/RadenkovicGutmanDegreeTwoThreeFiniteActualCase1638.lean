/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1638 : Family 10 := level10.get ⟨711,by decide⟩
def sourceMap1638 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1638 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1638_checked : acceptsGraphIso
    (source (graph core1638) (root 10) 0 2) DegreeTwoThreeSpectrum3442.graph sourceMap1638=true := by decide +kernel
theorem fusedMap1638_checked : acceptsGraphIso
    (fused (graph core1638) (root 10) 0 2) DegreeTwoThreeSpectrum2672.graph fusedMap1638=true := by decide +kernel
theorem certified1638 : Certified (graph core1638) (root 10) 0 2 :=
  of_native_maps core1638 DegreeTwoThreeSpectrum3442.graph DegreeTwoThreeSpectrum2672.graph
    sourceMap1638 fusedMap1638 sourceMap1638_checked fusedMap1638_checked
    DegreeTwoThreeFiniteComparisons.comparison1638
#print axioms sourceMap1638_checked
#print axioms fusedMap1638_checked
#print axioms certified1638
def sourceMap1638swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1638swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1638swap_checked : acceptsGraphIso
    (source (graph core1638) (root 10) 2 0) DegreeTwoThreeSpectrum3442.graph sourceMap1638swap=true := by decide +kernel
theorem fusedMap1638swap_checked : acceptsGraphIso
    (fused (graph core1638) (root 10) 2 0) DegreeTwoThreeSpectrum2672.graph fusedMap1638swap=true := by decide +kernel
theorem certified1638swap : Certified (graph core1638) (root 10) 2 0 :=
  of_native_maps core1638 DegreeTwoThreeSpectrum3442.graph DegreeTwoThreeSpectrum2672.graph
    sourceMap1638swap fusedMap1638swap sourceMap1638swap_checked fusedMap1638swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1638
#print axioms sourceMap1638swap_checked
#print axioms fusedMap1638swap_checked
#print axioms certified1638swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
