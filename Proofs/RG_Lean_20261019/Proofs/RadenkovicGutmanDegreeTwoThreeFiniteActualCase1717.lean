/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1717 : Family 10 := level10.get ⟨920,by decide⟩
def sourceMap1717 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,9,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1717 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1717_checked : acceptsGraphIso
    (source (graph core1717) (root 10) 0 2) DegreeTwoThreeSpectrum3644.graph sourceMap1717=true := by decide +kernel
theorem fusedMap1717_checked : acceptsGraphIso
    (fused (graph core1717) (root 10) 0 2) DegreeTwoThreeSpectrum2935.graph fusedMap1717=true := by decide +kernel
theorem certified1717 : Certified (graph core1717) (root 10) 0 2 :=
  of_native_maps core1717 DegreeTwoThreeSpectrum3644.graph DegreeTwoThreeSpectrum2935.graph
    sourceMap1717 fusedMap1717 sourceMap1717_checked fusedMap1717_checked
    DegreeTwoThreeFiniteComparisons.comparison1717
#print axioms sourceMap1717_checked
#print axioms fusedMap1717_checked
#print axioms certified1717
def sourceMap1717swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,2,3,4,9] (sourceLabel 10 2 0 v)
def fusedMap1717swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1717swap_checked : acceptsGraphIso
    (source (graph core1717) (root 10) 2 0) DegreeTwoThreeSpectrum3644.graph sourceMap1717swap=true := by decide +kernel
theorem fusedMap1717swap_checked : acceptsGraphIso
    (fused (graph core1717) (root 10) 2 0) DegreeTwoThreeSpectrum2935.graph fusedMap1717swap=true := by decide +kernel
theorem certified1717swap : Certified (graph core1717) (root 10) 2 0 :=
  of_native_maps core1717 DegreeTwoThreeSpectrum3644.graph DegreeTwoThreeSpectrum2935.graph
    sourceMap1717swap fusedMap1717swap sourceMap1717swap_checked fusedMap1717swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1717
#print axioms sourceMap1717swap_checked
#print axioms fusedMap1717swap_checked
#print axioms certified1717swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
