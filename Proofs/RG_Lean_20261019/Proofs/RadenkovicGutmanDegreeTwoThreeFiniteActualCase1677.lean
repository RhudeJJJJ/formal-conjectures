/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1677 : Family 10 := level10.get ⟨818,by decide⟩
def sourceMap1677 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,10,11,12,13,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1677 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1677_checked : acceptsGraphIso
    (source (graph core1677) (root 10) 0 2) DegreeTwoThreeSpectrum3596.graph sourceMap1677=true := by decide +kernel
theorem fusedMap1677_checked : acceptsGraphIso
    (fused (graph core1677) (root 10) 0 2) DegreeTwoThreeSpectrum2792.graph fusedMap1677=true := by decide +kernel
theorem certified1677 : Certified (graph core1677) (root 10) 0 2 :=
  of_native_maps core1677 DegreeTwoThreeSpectrum3596.graph DegreeTwoThreeSpectrum2792.graph
    sourceMap1677 fusedMap1677 sourceMap1677_checked fusedMap1677_checked
    DegreeTwoThreeFiniteComparisons.comparison1677
#print axioms sourceMap1677_checked
#print axioms fusedMap1677_checked
#print axioms certified1677
def sourceMap1677swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,10,11,12,7,8,9,13] (sourceLabel 10 2 0 v)
def fusedMap1677swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1677swap_checked : acceptsGraphIso
    (source (graph core1677) (root 10) 2 0) DegreeTwoThreeSpectrum3596.graph sourceMap1677swap=true := by decide +kernel
theorem fusedMap1677swap_checked : acceptsGraphIso
    (fused (graph core1677) (root 10) 2 0) DegreeTwoThreeSpectrum2792.graph fusedMap1677swap=true := by decide +kernel
theorem certified1677swap : Certified (graph core1677) (root 10) 2 0 :=
  of_native_maps core1677 DegreeTwoThreeSpectrum3596.graph DegreeTwoThreeSpectrum2792.graph
    sourceMap1677swap fusedMap1677swap sourceMap1677swap_checked fusedMap1677swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1677
#print axioms sourceMap1677swap_checked
#print axioms fusedMap1677swap_checked
#print axioms certified1677swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
