/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1389 : Family 9 := level9.get ⟨573,by decide⟩
def sourceMap1389 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1389 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1389_checked : acceptsGraphIso
    (source (graph core1389) (root 9) 0 2) DegreeTwoThreeSpectrum2260.graph sourceMap1389=true := by decide +kernel
theorem fusedMap1389_checked : acceptsGraphIso
    (fused (graph core1389) (root 9) 0 2) DegreeTwoThreeSpectrum1961.graph fusedMap1389=true := by decide +kernel
theorem certified1389 : Certified (graph core1389) (root 9) 0 2 :=
  of_native_maps core1389 DegreeTwoThreeSpectrum2260.graph DegreeTwoThreeSpectrum1961.graph
    sourceMap1389 fusedMap1389 sourceMap1389_checked fusedMap1389_checked
    DegreeTwoThreeFiniteComparisons.comparison1389
#print axioms sourceMap1389_checked
#print axioms fusedMap1389_checked
#print axioms certified1389
def sourceMap1389swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1389swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1389swap_checked : acceptsGraphIso
    (source (graph core1389) (root 9) 2 0) DegreeTwoThreeSpectrum2260.graph sourceMap1389swap=true := by decide +kernel
theorem fusedMap1389swap_checked : acceptsGraphIso
    (fused (graph core1389) (root 9) 2 0) DegreeTwoThreeSpectrum1961.graph fusedMap1389swap=true := by decide +kernel
theorem certified1389swap : Certified (graph core1389) (root 9) 2 0 :=
  of_native_maps core1389 DegreeTwoThreeSpectrum2260.graph DegreeTwoThreeSpectrum1961.graph
    sourceMap1389swap fusedMap1389swap sourceMap1389swap_checked fusedMap1389swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1389
#print axioms sourceMap1389swap_checked
#print axioms fusedMap1389swap_checked
#print axioms certified1389swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
