/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1686 : Family 10 := level10.get ⟨846,by decide⟩
def sourceMap1686 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1686 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1686_checked : acceptsGraphIso
    (source (graph core1686) (root 10) 0 2) DegreeTwoThreeSpectrum3658.graph sourceMap1686=true := by decide +kernel
theorem fusedMap1686_checked : acceptsGraphIso
    (fused (graph core1686) (root 10) 0 2) DegreeTwoThreeSpectrum2833.graph fusedMap1686=true := by decide +kernel
theorem certified1686 : Certified (graph core1686) (root 10) 0 2 :=
  of_native_maps core1686 DegreeTwoThreeSpectrum3658.graph DegreeTwoThreeSpectrum2833.graph
    sourceMap1686 fusedMap1686 sourceMap1686_checked fusedMap1686_checked
    DegreeTwoThreeFiniteComparisons.comparison1686
#print axioms sourceMap1686_checked
#print axioms fusedMap1686_checked
#print axioms certified1686
def sourceMap1686swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1686swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1686swap_checked : acceptsGraphIso
    (source (graph core1686) (root 10) 2 0) DegreeTwoThreeSpectrum3658.graph sourceMap1686swap=true := by decide +kernel
theorem fusedMap1686swap_checked : acceptsGraphIso
    (fused (graph core1686) (root 10) 2 0) DegreeTwoThreeSpectrum2833.graph fusedMap1686swap=true := by decide +kernel
theorem certified1686swap : Certified (graph core1686) (root 10) 2 0 :=
  of_native_maps core1686 DegreeTwoThreeSpectrum3658.graph DegreeTwoThreeSpectrum2833.graph
    sourceMap1686swap fusedMap1686swap sourceMap1686swap_checked fusedMap1686swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1686
#print axioms sourceMap1686swap_checked
#print axioms fusedMap1686swap_checked
#print axioms certified1686swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
