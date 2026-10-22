/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1674 : Family 10 := level10.get ⟨814,by decide⟩
def sourceMap1674 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1674 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1674_checked : acceptsGraphIso
    (source (graph core1674) (root 10) 0 2) DegreeTwoThreeSpectrum3602.graph sourceMap1674=true := by decide +kernel
theorem fusedMap1674_checked : acceptsGraphIso
    (fused (graph core1674) (root 10) 0 2) DegreeTwoThreeSpectrum2784.graph fusedMap1674=true := by decide +kernel
theorem certified1674 : Certified (graph core1674) (root 10) 0 2 :=
  of_native_maps core1674 DegreeTwoThreeSpectrum3602.graph DegreeTwoThreeSpectrum2784.graph
    sourceMap1674 fusedMap1674 sourceMap1674_checked fusedMap1674_checked
    DegreeTwoThreeFiniteComparisons.comparison1674
#print axioms sourceMap1674_checked
#print axioms fusedMap1674_checked
#print axioms certified1674
def sourceMap1674swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1674swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1674swap_checked : acceptsGraphIso
    (source (graph core1674) (root 10) 2 0) DegreeTwoThreeSpectrum3602.graph sourceMap1674swap=true := by decide +kernel
theorem fusedMap1674swap_checked : acceptsGraphIso
    (fused (graph core1674) (root 10) 2 0) DegreeTwoThreeSpectrum2784.graph fusedMap1674swap=true := by decide +kernel
theorem certified1674swap : Certified (graph core1674) (root 10) 2 0 :=
  of_native_maps core1674 DegreeTwoThreeSpectrum3602.graph DegreeTwoThreeSpectrum2784.graph
    sourceMap1674swap fusedMap1674swap sourceMap1674swap_checked fusedMap1674swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1674
#print axioms sourceMap1674swap_checked
#print axioms fusedMap1674swap_checked
#print axioms certified1674swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
