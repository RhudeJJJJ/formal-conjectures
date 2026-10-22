/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1718 : Family 10 := level10.get ⟨926,by decide⟩
def sourceMap1718 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1718 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1718_checked : acceptsGraphIso
    (source (graph core1718) (root 10) 0 2) DegreeTwoThreeSpectrum3707.graph sourceMap1718=true := by decide +kernel
theorem fusedMap1718_checked : acceptsGraphIso
    (fused (graph core1718) (root 10) 0 2) DegreeTwoThreeSpectrum2942.graph fusedMap1718=true := by decide +kernel
theorem certified1718 : Certified (graph core1718) (root 10) 0 2 :=
  of_native_maps core1718 DegreeTwoThreeSpectrum3707.graph DegreeTwoThreeSpectrum2942.graph
    sourceMap1718 fusedMap1718 sourceMap1718_checked fusedMap1718_checked
    DegreeTwoThreeFiniteComparisons.comparison1718
#print axioms sourceMap1718_checked
#print axioms fusedMap1718_checked
#print axioms certified1718
def sourceMap1718swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1718swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1718swap_checked : acceptsGraphIso
    (source (graph core1718) (root 10) 2 0) DegreeTwoThreeSpectrum3707.graph sourceMap1718swap=true := by decide +kernel
theorem fusedMap1718swap_checked : acceptsGraphIso
    (fused (graph core1718) (root 10) 2 0) DegreeTwoThreeSpectrum2942.graph fusedMap1718swap=true := by decide +kernel
theorem certified1718swap : Certified (graph core1718) (root 10) 2 0 :=
  of_native_maps core1718 DegreeTwoThreeSpectrum3707.graph DegreeTwoThreeSpectrum2942.graph
    sourceMap1718swap fusedMap1718swap sourceMap1718swap_checked fusedMap1718swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1718
#print axioms sourceMap1718swap_checked
#print axioms fusedMap1718swap_checked
#print axioms certified1718swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
