/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1305 : Family 9 := level9.get ⟨371,by decide⟩
def sourceMap1305 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1305 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1305_checked : acceptsGraphIso
    (source (graph core1305) (root 9) 0 2) DegreeTwoThreeSpectrum2014.graph sourceMap1305=true := by decide +kernel
theorem fusedMap1305_checked : acceptsGraphIso
    (fused (graph core1305) (root 9) 0 2) DegreeTwoThreeSpectrum2015.graph fusedMap1305=true := by decide +kernel
theorem certified1305 : Certified (graph core1305) (root 9) 0 2 :=
  of_native_maps core1305 DegreeTwoThreeSpectrum2014.graph DegreeTwoThreeSpectrum2015.graph
    sourceMap1305 fusedMap1305 sourceMap1305_checked fusedMap1305_checked
    DegreeTwoThreeFiniteComparisons.comparison1305
#print axioms sourceMap1305_checked
#print axioms fusedMap1305_checked
#print axioms certified1305
def sourceMap1305swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1305swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1305swap_checked : acceptsGraphIso
    (source (graph core1305) (root 9) 2 0) DegreeTwoThreeSpectrum2014.graph sourceMap1305swap=true := by decide +kernel
theorem fusedMap1305swap_checked : acceptsGraphIso
    (fused (graph core1305) (root 9) 2 0) DegreeTwoThreeSpectrum2015.graph fusedMap1305swap=true := by decide +kernel
theorem certified1305swap : Certified (graph core1305) (root 9) 2 0 :=
  of_native_maps core1305 DegreeTwoThreeSpectrum2014.graph DegreeTwoThreeSpectrum2015.graph
    sourceMap1305swap fusedMap1305swap sourceMap1305swap_checked fusedMap1305swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1305
#print axioms sourceMap1305swap_checked
#print axioms fusedMap1305swap_checked
#print axioms certified1305swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
