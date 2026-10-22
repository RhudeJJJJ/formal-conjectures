/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1564 : Family 10 := level10.get ⟨488,by decide⟩
def sourceMap1564 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1564 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1564_checked : acceptsGraphIso
    (source (graph core1564) (root 10) 0 2) DegreeTwoThreeSpectrum2956.graph sourceMap1564=true := by decide +kernel
theorem fusedMap1564_checked : acceptsGraphIso
    (fused (graph core1564) (root 10) 0 2) DegreeTwoThreeSpectrum2943.graph fusedMap1564=true := by decide +kernel
theorem certified1564 : Certified (graph core1564) (root 10) 0 2 :=
  of_native_maps core1564 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2943.graph
    sourceMap1564 fusedMap1564 sourceMap1564_checked fusedMap1564_checked
    DegreeTwoThreeFiniteComparisons.comparison1564
#print axioms sourceMap1564_checked
#print axioms fusedMap1564_checked
#print axioms certified1564
def sourceMap1564swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1564swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1564swap_checked : acceptsGraphIso
    (source (graph core1564) (root 10) 2 0) DegreeTwoThreeSpectrum2956.graph sourceMap1564swap=true := by decide +kernel
theorem fusedMap1564swap_checked : acceptsGraphIso
    (fused (graph core1564) (root 10) 2 0) DegreeTwoThreeSpectrum2943.graph fusedMap1564swap=true := by decide +kernel
theorem certified1564swap : Certified (graph core1564) (root 10) 2 0 :=
  of_native_maps core1564 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2943.graph
    sourceMap1564swap fusedMap1564swap sourceMap1564swap_checked fusedMap1564swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1564
#print axioms sourceMap1564swap_checked
#print axioms fusedMap1564swap_checked
#print axioms certified1564swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
