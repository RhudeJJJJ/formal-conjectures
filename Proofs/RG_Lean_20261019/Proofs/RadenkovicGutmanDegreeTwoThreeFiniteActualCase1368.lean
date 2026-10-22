/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1368 : Family 9 := level9.get ⟨518,by decide⟩
def sourceMap1368 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1368 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1368_checked : acceptsGraphIso
    (source (graph core1368) (root 9) 0 2) DegreeTwoThreeSpectrum2041.graph sourceMap1368=true := by decide +kernel
theorem fusedMap1368_checked : acceptsGraphIso
    (fused (graph core1368) (root 9) 0 2) DegreeTwoThreeSpectrum2230.graph fusedMap1368=true := by decide +kernel
theorem certified1368 : Certified (graph core1368) (root 9) 0 2 :=
  of_native_maps core1368 DegreeTwoThreeSpectrum2041.graph DegreeTwoThreeSpectrum2230.graph
    sourceMap1368 fusedMap1368 sourceMap1368_checked fusedMap1368_checked
    DegreeTwoThreeFiniteComparisons.comparison1368
#print axioms sourceMap1368_checked
#print axioms fusedMap1368_checked
#print axioms certified1368
def sourceMap1368swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1368swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1368swap_checked : acceptsGraphIso
    (source (graph core1368) (root 9) 2 0) DegreeTwoThreeSpectrum2041.graph sourceMap1368swap=true := by decide +kernel
theorem fusedMap1368swap_checked : acceptsGraphIso
    (fused (graph core1368) (root 9) 2 0) DegreeTwoThreeSpectrum2230.graph fusedMap1368swap=true := by decide +kernel
theorem certified1368swap : Certified (graph core1368) (root 9) 2 0 :=
  of_native_maps core1368 DegreeTwoThreeSpectrum2041.graph DegreeTwoThreeSpectrum2230.graph
    sourceMap1368swap fusedMap1368swap sourceMap1368swap_checked fusedMap1368swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1368
#print axioms sourceMap1368swap_checked
#print axioms fusedMap1368swap_checked
#print axioms certified1368swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
