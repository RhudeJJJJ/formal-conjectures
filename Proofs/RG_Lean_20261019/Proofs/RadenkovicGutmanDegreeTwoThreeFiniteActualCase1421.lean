/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1421 : Family 9 := level9.get ⟨653,by decide⟩
def sourceMap1421 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1421 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1421_checked : acceptsGraphIso
    (source (graph core1421) (root 9) 0 2) DegreeTwoThreeSpectrum2297.graph sourceMap1421=true := by decide +kernel
theorem fusedMap1421_checked : acceptsGraphIso
    (fused (graph core1421) (root 9) 0 2) DegreeTwoThreeSpectrum2116.graph fusedMap1421=true := by decide +kernel
theorem certified1421 : Certified (graph core1421) (root 9) 0 2 :=
  of_native_maps core1421 DegreeTwoThreeSpectrum2297.graph DegreeTwoThreeSpectrum2116.graph
    sourceMap1421 fusedMap1421 sourceMap1421_checked fusedMap1421_checked
    DegreeTwoThreeFiniteComparisons.comparison1421
#print axioms sourceMap1421_checked
#print axioms fusedMap1421_checked
#print axioms certified1421
def sourceMap1421swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1421swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1421swap_checked : acceptsGraphIso
    (source (graph core1421) (root 9) 2 0) DegreeTwoThreeSpectrum2297.graph sourceMap1421swap=true := by decide +kernel
theorem fusedMap1421swap_checked : acceptsGraphIso
    (fused (graph core1421) (root 9) 2 0) DegreeTwoThreeSpectrum2116.graph fusedMap1421swap=true := by decide +kernel
theorem certified1421swap : Certified (graph core1421) (root 9) 2 0 :=
  of_native_maps core1421 DegreeTwoThreeSpectrum2297.graph DegreeTwoThreeSpectrum2116.graph
    sourceMap1421swap fusedMap1421swap sourceMap1421swap_checked fusedMap1421swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1421
#print axioms sourceMap1421swap_checked
#print axioms fusedMap1421swap_checked
#print axioms certified1421swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
