/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1424 : Family 9 := level9.get ⟨659,by decide⟩
def sourceMap1424 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1424 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1424_checked : acceptsGraphIso
    (source (graph core1424) (root 9) 0 2) DegreeTwoThreeSpectrum2301.graph sourceMap1424=true := by decide +kernel
theorem fusedMap1424_checked : acceptsGraphIso
    (fused (graph core1424) (root 9) 0 2) DegreeTwoThreeSpectrum2126.graph fusedMap1424=true := by decide +kernel
theorem certified1424 : Certified (graph core1424) (root 9) 0 2 :=
  of_native_maps core1424 DegreeTwoThreeSpectrum2301.graph DegreeTwoThreeSpectrum2126.graph
    sourceMap1424 fusedMap1424 sourceMap1424_checked fusedMap1424_checked
    DegreeTwoThreeFiniteComparisons.comparison1424
#print axioms sourceMap1424_checked
#print axioms fusedMap1424_checked
#print axioms certified1424
def sourceMap1424swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1424swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1424swap_checked : acceptsGraphIso
    (source (graph core1424) (root 9) 2 0) DegreeTwoThreeSpectrum2301.graph sourceMap1424swap=true := by decide +kernel
theorem fusedMap1424swap_checked : acceptsGraphIso
    (fused (graph core1424) (root 9) 2 0) DegreeTwoThreeSpectrum2126.graph fusedMap1424swap=true := by decide +kernel
theorem certified1424swap : Certified (graph core1424) (root 9) 2 0 :=
  of_native_maps core1424 DegreeTwoThreeSpectrum2301.graph DegreeTwoThreeSpectrum2126.graph
    sourceMap1424swap fusedMap1424swap sourceMap1424swap_checked fusedMap1424swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1424
#print axioms sourceMap1424swap_checked
#print axioms fusedMap1424swap_checked
#print axioms certified1424swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
