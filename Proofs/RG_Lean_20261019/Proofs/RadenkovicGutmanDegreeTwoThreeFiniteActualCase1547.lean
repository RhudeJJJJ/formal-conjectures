/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1547 : Family 10 := level10.get ⟨445,by decide⟩
def sourceMap1547 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1547 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1547_checked : acceptsGraphIso
    (source (graph core1547) (root 10) 0 2) DegreeTwoThreeSpectrum2853.graph sourceMap1547=true := by decide +kernel
theorem fusedMap1547_checked : acceptsGraphIso
    (fused (graph core1547) (root 10) 0 2) DegreeTwoThreeSpectrum2977.graph fusedMap1547=true := by decide +kernel
theorem certified1547 : Certified (graph core1547) (root 10) 0 2 :=
  of_native_maps core1547 DegreeTwoThreeSpectrum2853.graph DegreeTwoThreeSpectrum2977.graph
    sourceMap1547 fusedMap1547 sourceMap1547_checked fusedMap1547_checked
    DegreeTwoThreeFiniteComparisons.comparison1547
#print axioms sourceMap1547_checked
#print axioms fusedMap1547_checked
#print axioms certified1547
def sourceMap1547swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1547swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1547swap_checked : acceptsGraphIso
    (source (graph core1547) (root 10) 2 0) DegreeTwoThreeSpectrum2853.graph sourceMap1547swap=true := by decide +kernel
theorem fusedMap1547swap_checked : acceptsGraphIso
    (fused (graph core1547) (root 10) 2 0) DegreeTwoThreeSpectrum2977.graph fusedMap1547swap=true := by decide +kernel
theorem certified1547swap : Certified (graph core1547) (root 10) 2 0 :=
  of_native_maps core1547 DegreeTwoThreeSpectrum2853.graph DegreeTwoThreeSpectrum2977.graph
    sourceMap1547swap fusedMap1547swap sourceMap1547swap_checked fusedMap1547swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1547
#print axioms sourceMap1547swap_checked
#print axioms fusedMap1547swap_checked
#print axioms certified1547swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
