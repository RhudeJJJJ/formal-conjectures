/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1672 : Family 10 := level10.get ⟨810,by decide⟩
def sourceMap1672 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1672 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1672_checked : acceptsGraphIso
    (source (graph core1672) (root 10) 0 2) DegreeTwoThreeSpectrum3601.graph sourceMap1672=true := by decide +kernel
theorem fusedMap1672_checked : acceptsGraphIso
    (fused (graph core1672) (root 10) 0 2) DegreeTwoThreeSpectrum2779.graph fusedMap1672=true := by decide +kernel
theorem certified1672 : Certified (graph core1672) (root 10) 0 2 :=
  of_native_maps core1672 DegreeTwoThreeSpectrum3601.graph DegreeTwoThreeSpectrum2779.graph
    sourceMap1672 fusedMap1672 sourceMap1672_checked fusedMap1672_checked
    DegreeTwoThreeFiniteComparisons.comparison1672
#print axioms sourceMap1672_checked
#print axioms fusedMap1672_checked
#print axioms certified1672
def sourceMap1672swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1672swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1672swap_checked : acceptsGraphIso
    (source (graph core1672) (root 10) 2 0) DegreeTwoThreeSpectrum3601.graph sourceMap1672swap=true := by decide +kernel
theorem fusedMap1672swap_checked : acceptsGraphIso
    (fused (graph core1672) (root 10) 2 0) DegreeTwoThreeSpectrum2779.graph fusedMap1672swap=true := by decide +kernel
theorem certified1672swap : Certified (graph core1672) (root 10) 2 0 :=
  of_native_maps core1672 DegreeTwoThreeSpectrum3601.graph DegreeTwoThreeSpectrum2779.graph
    sourceMap1672swap fusedMap1672swap sourceMap1672swap_checked fusedMap1672swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1672
#print axioms sourceMap1672swap_checked
#print axioms fusedMap1672swap_checked
#print axioms certified1672swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
