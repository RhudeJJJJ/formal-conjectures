/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1789 : Family 10 := level10.get ⟨1108,by decide⟩
def sourceMap1789 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1789 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1789_checked : acceptsGraphIso
    (source (graph core1789) (root 10) 0 2) DegreeTwoThreeSpectrum3177.graph sourceMap1789=true := by decide +kernel
theorem fusedMap1789_checked : acceptsGraphIso
    (fused (graph core1789) (root 10) 0 2) DegreeTwoThreeSpectrum3178.graph fusedMap1789=true := by decide +kernel
theorem certified1789 : Certified (graph core1789) (root 10) 0 2 :=
  of_native_maps core1789 DegreeTwoThreeSpectrum3177.graph DegreeTwoThreeSpectrum3178.graph
    sourceMap1789 fusedMap1789 sourceMap1789_checked fusedMap1789_checked
    DegreeTwoThreeFiniteComparisons.comparison1789
#print axioms sourceMap1789_checked
#print axioms fusedMap1789_checked
#print axioms certified1789
def sourceMap1789swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1789swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1789swap_checked : acceptsGraphIso
    (source (graph core1789) (root 10) 2 0) DegreeTwoThreeSpectrum3177.graph sourceMap1789swap=true := by decide +kernel
theorem fusedMap1789swap_checked : acceptsGraphIso
    (fused (graph core1789) (root 10) 2 0) DegreeTwoThreeSpectrum3178.graph fusedMap1789swap=true := by decide +kernel
theorem certified1789swap : Certified (graph core1789) (root 10) 2 0 :=
  of_native_maps core1789 DegreeTwoThreeSpectrum3177.graph DegreeTwoThreeSpectrum3178.graph
    sourceMap1789swap fusedMap1789swap sourceMap1789swap_checked fusedMap1789swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1789
#print axioms sourceMap1789swap_checked
#print axioms fusedMap1789swap_checked
#print axioms certified1789swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
