/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1598 : Family 10 := level10.get ⟨600,by decide⟩
def sourceMap1598 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1598 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1598_checked : acceptsGraphIso
    (source (graph core1598) (root 10) 0 2) DegreeTwoThreeSpectrum3262.graph sourceMap1598=true := by decide +kernel
theorem fusedMap1598_checked : acceptsGraphIso
    (fused (graph core1598) (root 10) 0 2) DegreeTwoThreeSpectrum2540.graph fusedMap1598=true := by decide +kernel
theorem certified1598 : Certified (graph core1598) (root 10) 0 2 :=
  of_native_maps core1598 DegreeTwoThreeSpectrum3262.graph DegreeTwoThreeSpectrum2540.graph
    sourceMap1598 fusedMap1598 sourceMap1598_checked fusedMap1598_checked
    DegreeTwoThreeFiniteComparisons.comparison1598
#print axioms sourceMap1598_checked
#print axioms fusedMap1598_checked
#print axioms certified1598
def sourceMap1598swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1598swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1598swap_checked : acceptsGraphIso
    (source (graph core1598) (root 10) 2 0) DegreeTwoThreeSpectrum3262.graph sourceMap1598swap=true := by decide +kernel
theorem fusedMap1598swap_checked : acceptsGraphIso
    (fused (graph core1598) (root 10) 2 0) DegreeTwoThreeSpectrum2540.graph fusedMap1598swap=true := by decide +kernel
theorem certified1598swap : Certified (graph core1598) (root 10) 2 0 :=
  of_native_maps core1598 DegreeTwoThreeSpectrum3262.graph DegreeTwoThreeSpectrum2540.graph
    sourceMap1598swap fusedMap1598swap sourceMap1598swap_checked fusedMap1598swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1598
#print axioms sourceMap1598swap_checked
#print axioms fusedMap1598swap_checked
#print axioms certified1598swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
