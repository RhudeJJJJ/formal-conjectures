/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1565 : Family 10 := level10.get ⟨489,by decide⟩
def sourceMap1565 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1565 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1565_checked : acceptsGraphIso
    (source (graph core1565) (root 10) 0 2) DegreeTwoThreeSpectrum2563.graph sourceMap1565=true := by decide +kernel
theorem fusedMap1565_checked : acceptsGraphIso
    (fused (graph core1565) (root 10) 0 2) DegreeTwoThreeSpectrum2948.graph fusedMap1565=true := by decide +kernel
theorem certified1565 : Certified (graph core1565) (root 10) 0 2 :=
  of_native_maps core1565 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2948.graph
    sourceMap1565 fusedMap1565 sourceMap1565_checked fusedMap1565_checked
    DegreeTwoThreeFiniteComparisons.comparison1565
#print axioms sourceMap1565_checked
#print axioms fusedMap1565_checked
#print axioms certified1565
def sourceMap1565swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1565swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1565swap_checked : acceptsGraphIso
    (source (graph core1565) (root 10) 2 0) DegreeTwoThreeSpectrum2563.graph sourceMap1565swap=true := by decide +kernel
theorem fusedMap1565swap_checked : acceptsGraphIso
    (fused (graph core1565) (root 10) 2 0) DegreeTwoThreeSpectrum2948.graph fusedMap1565swap=true := by decide +kernel
theorem certified1565swap : Certified (graph core1565) (root 10) 2 0 :=
  of_native_maps core1565 DegreeTwoThreeSpectrum2563.graph DegreeTwoThreeSpectrum2948.graph
    sourceMap1565swap fusedMap1565swap sourceMap1565swap_checked fusedMap1565swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1565
#print axioms sourceMap1565swap_checked
#print axioms fusedMap1565swap_checked
#print axioms certified1565swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
