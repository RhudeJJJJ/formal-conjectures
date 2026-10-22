/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1636 : Family 10 := level10.get ⟨707,by decide⟩
def sourceMap1636 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1636 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1636_checked : acceptsGraphIso
    (source (graph core1636) (root 10) 0 2) DegreeTwoThreeSpectrum3438.graph sourceMap1636=true := by decide +kernel
theorem fusedMap1636_checked : acceptsGraphIso
    (fused (graph core1636) (root 10) 0 2) DegreeTwoThreeSpectrum2666.graph fusedMap1636=true := by decide +kernel
theorem certified1636 : Certified (graph core1636) (root 10) 0 2 :=
  of_native_maps core1636 DegreeTwoThreeSpectrum3438.graph DegreeTwoThreeSpectrum2666.graph
    sourceMap1636 fusedMap1636 sourceMap1636_checked fusedMap1636_checked
    DegreeTwoThreeFiniteComparisons.comparison1636
#print axioms sourceMap1636_checked
#print axioms fusedMap1636_checked
#print axioms certified1636
def sourceMap1636swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1636swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1636swap_checked : acceptsGraphIso
    (source (graph core1636) (root 10) 2 0) DegreeTwoThreeSpectrum3438.graph sourceMap1636swap=true := by decide +kernel
theorem fusedMap1636swap_checked : acceptsGraphIso
    (fused (graph core1636) (root 10) 2 0) DegreeTwoThreeSpectrum2666.graph fusedMap1636swap=true := by decide +kernel
theorem certified1636swap : Certified (graph core1636) (root 10) 2 0 :=
  of_native_maps core1636 DegreeTwoThreeSpectrum3438.graph DegreeTwoThreeSpectrum2666.graph
    sourceMap1636swap fusedMap1636swap sourceMap1636swap_checked fusedMap1636swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1636
#print axioms sourceMap1636swap_checked
#print axioms fusedMap1636swap_checked
#print axioms certified1636swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
