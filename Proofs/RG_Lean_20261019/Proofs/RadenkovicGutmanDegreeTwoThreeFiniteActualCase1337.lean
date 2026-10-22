/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1337 : Family 9 := level9.get ⟨451,by decide⟩
def sourceMap1337 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1337 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1337_checked : acceptsGraphIso
    (source (graph core1337) (root 9) 0 2) DegreeTwoThreeSpectrum2130.graph sourceMap1337=true := by decide +kernel
theorem fusedMap1337_checked : acceptsGraphIso
    (fused (graph core1337) (root 9) 0 2) DegreeTwoThreeSpectrum2131.graph fusedMap1337=true := by decide +kernel
theorem certified1337 : Certified (graph core1337) (root 9) 0 2 :=
  of_native_maps core1337 DegreeTwoThreeSpectrum2130.graph DegreeTwoThreeSpectrum2131.graph
    sourceMap1337 fusedMap1337 sourceMap1337_checked fusedMap1337_checked
    DegreeTwoThreeFiniteComparisons.comparison1337
#print axioms sourceMap1337_checked
#print axioms fusedMap1337_checked
#print axioms certified1337
def sourceMap1337swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1337swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1337swap_checked : acceptsGraphIso
    (source (graph core1337) (root 9) 2 0) DegreeTwoThreeSpectrum2130.graph sourceMap1337swap=true := by decide +kernel
theorem fusedMap1337swap_checked : acceptsGraphIso
    (fused (graph core1337) (root 9) 2 0) DegreeTwoThreeSpectrum2131.graph fusedMap1337swap=true := by decide +kernel
theorem certified1337swap : Certified (graph core1337) (root 9) 2 0 :=
  of_native_maps core1337 DegreeTwoThreeSpectrum2130.graph DegreeTwoThreeSpectrum2131.graph
    sourceMap1337swap fusedMap1337swap sourceMap1337swap_checked fusedMap1337swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1337
#print axioms sourceMap1337swap_checked
#print axioms fusedMap1337swap_checked
#print axioms certified1337swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
