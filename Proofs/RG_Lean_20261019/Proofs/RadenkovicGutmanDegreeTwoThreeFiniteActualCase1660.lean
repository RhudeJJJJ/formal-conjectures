/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1660 : Family 10 := level10.get ⟨777,by decide⟩
def sourceMap1660 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1660 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1660_checked : acceptsGraphIso
    (source (graph core1660) (root 10) 0 2) DegreeTwoThreeSpectrum3562.graph sourceMap1660=true := by decide +kernel
theorem fusedMap1660_checked : acceptsGraphIso
    (fused (graph core1660) (root 10) 0 2) DegreeTwoThreeSpectrum2743.graph fusedMap1660=true := by decide +kernel
theorem certified1660 : Certified (graph core1660) (root 10) 0 2 :=
  of_native_maps core1660 DegreeTwoThreeSpectrum3562.graph DegreeTwoThreeSpectrum2743.graph
    sourceMap1660 fusedMap1660 sourceMap1660_checked fusedMap1660_checked
    DegreeTwoThreeFiniteComparisons.comparison1660
#print axioms sourceMap1660_checked
#print axioms fusedMap1660_checked
#print axioms certified1660
def sourceMap1660swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1660swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1660swap_checked : acceptsGraphIso
    (source (graph core1660) (root 10) 2 0) DegreeTwoThreeSpectrum3562.graph sourceMap1660swap=true := by decide +kernel
theorem fusedMap1660swap_checked : acceptsGraphIso
    (fused (graph core1660) (root 10) 2 0) DegreeTwoThreeSpectrum2743.graph fusedMap1660swap=true := by decide +kernel
theorem certified1660swap : Certified (graph core1660) (root 10) 2 0 :=
  of_native_maps core1660 DegreeTwoThreeSpectrum3562.graph DegreeTwoThreeSpectrum2743.graph
    sourceMap1660swap fusedMap1660swap sourceMap1660swap_checked fusedMap1660swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1660
#print axioms sourceMap1660swap_checked
#print axioms fusedMap1660swap_checked
#print axioms certified1660swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
