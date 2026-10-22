/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1619 : Family 10 := level10.get ⟨660,by decide⟩
def sourceMap1619 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1619 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1619_checked : acceptsGraphIso
    (source (graph core1619) (root 10) 0 2) DegreeTwoThreeSpectrum3366.graph sourceMap1619=true := by decide +kernel
theorem fusedMap1619_checked : acceptsGraphIso
    (fused (graph core1619) (root 10) 0 2) DegreeTwoThreeSpectrum2607.graph fusedMap1619=true := by decide +kernel
theorem certified1619 : Certified (graph core1619) (root 10) 0 2 :=
  of_native_maps core1619 DegreeTwoThreeSpectrum3366.graph DegreeTwoThreeSpectrum2607.graph
    sourceMap1619 fusedMap1619 sourceMap1619_checked fusedMap1619_checked
    DegreeTwoThreeFiniteComparisons.comparison1619
#print axioms sourceMap1619_checked
#print axioms fusedMap1619_checked
#print axioms certified1619
def sourceMap1619swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1619swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1619swap_checked : acceptsGraphIso
    (source (graph core1619) (root 10) 2 0) DegreeTwoThreeSpectrum3366.graph sourceMap1619swap=true := by decide +kernel
theorem fusedMap1619swap_checked : acceptsGraphIso
    (fused (graph core1619) (root 10) 2 0) DegreeTwoThreeSpectrum2607.graph fusedMap1619swap=true := by decide +kernel
theorem certified1619swap : Certified (graph core1619) (root 10) 2 0 :=
  of_native_maps core1619 DegreeTwoThreeSpectrum3366.graph DegreeTwoThreeSpectrum2607.graph
    sourceMap1619swap fusedMap1619swap sourceMap1619swap_checked fusedMap1619swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1619
#print axioms sourceMap1619swap_checked
#print axioms fusedMap1619swap_checked
#print axioms certified1619swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
