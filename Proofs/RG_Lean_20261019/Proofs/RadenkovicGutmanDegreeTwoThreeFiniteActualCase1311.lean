/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1311 : Family 9 := level9.get ⟨383,by decide⟩
def sourceMap1311 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1311 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1311_checked : acceptsGraphIso
    (source (graph core1311) (root 9) 0 2) DegreeTwoThreeSpectrum2032.graph sourceMap1311=true := by decide +kernel
theorem fusedMap1311_checked : acceptsGraphIso
    (fused (graph core1311) (root 9) 0 2) DegreeTwoThreeSpectrum2036.graph fusedMap1311=true := by decide +kernel
theorem certified1311 : Certified (graph core1311) (root 9) 0 2 :=
  of_native_maps core1311 DegreeTwoThreeSpectrum2032.graph DegreeTwoThreeSpectrum2036.graph
    sourceMap1311 fusedMap1311 sourceMap1311_checked fusedMap1311_checked
    DegreeTwoThreeFiniteComparisons.comparison1311
#print axioms sourceMap1311_checked
#print axioms fusedMap1311_checked
#print axioms certified1311
def sourceMap1311swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1311swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1311swap_checked : acceptsGraphIso
    (source (graph core1311) (root 9) 2 0) DegreeTwoThreeSpectrum2032.graph sourceMap1311swap=true := by decide +kernel
theorem fusedMap1311swap_checked : acceptsGraphIso
    (fused (graph core1311) (root 9) 2 0) DegreeTwoThreeSpectrum2036.graph fusedMap1311swap=true := by decide +kernel
theorem certified1311swap : Certified (graph core1311) (root 9) 2 0 :=
  of_native_maps core1311 DegreeTwoThreeSpectrum2032.graph DegreeTwoThreeSpectrum2036.graph
    sourceMap1311swap fusedMap1311swap sourceMap1311swap_checked fusedMap1311swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1311
#print axioms sourceMap1311swap_checked
#print axioms fusedMap1311swap_checked
#print axioms certified1311swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
