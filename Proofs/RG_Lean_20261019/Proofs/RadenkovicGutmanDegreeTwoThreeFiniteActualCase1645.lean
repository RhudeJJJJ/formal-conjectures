/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1645 : Family 10 := level10.get ⟨732,by decide⟩
def sourceMap1645 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1645 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1645_checked : acceptsGraphIso
    (source (graph core1645) (root 10) 0 2) DegreeTwoThreeSpectrum3480.graph sourceMap1645=true := by decide +kernel
theorem fusedMap1645_checked : acceptsGraphIso
    (fused (graph core1645) (root 10) 0 2) DegreeTwoThreeSpectrum2694.graph fusedMap1645=true := by decide +kernel
theorem certified1645 : Certified (graph core1645) (root 10) 0 2 :=
  of_native_maps core1645 DegreeTwoThreeSpectrum3480.graph DegreeTwoThreeSpectrum2694.graph
    sourceMap1645 fusedMap1645 sourceMap1645_checked fusedMap1645_checked
    DegreeTwoThreeFiniteComparisons.comparison1645
#print axioms sourceMap1645_checked
#print axioms fusedMap1645_checked
#print axioms certified1645
def sourceMap1645swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1645swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1645swap_checked : acceptsGraphIso
    (source (graph core1645) (root 10) 2 0) DegreeTwoThreeSpectrum3480.graph sourceMap1645swap=true := by decide +kernel
theorem fusedMap1645swap_checked : acceptsGraphIso
    (fused (graph core1645) (root 10) 2 0) DegreeTwoThreeSpectrum2694.graph fusedMap1645swap=true := by decide +kernel
theorem certified1645swap : Certified (graph core1645) (root 10) 2 0 :=
  of_native_maps core1645 DegreeTwoThreeSpectrum3480.graph DegreeTwoThreeSpectrum2694.graph
    sourceMap1645swap fusedMap1645swap sourceMap1645swap_checked fusedMap1645swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1645
#print axioms sourceMap1645swap_checked
#print axioms fusedMap1645swap_checked
#print axioms certified1645swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
