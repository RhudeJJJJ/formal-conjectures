/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1344 : Family 9 := level9.get ⟨467,by decide⟩
def sourceMap1344 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1344 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1344_checked : acceptsGraphIso
    (source (graph core1344) (root 9) 0 2) DegreeTwoThreeSpectrum2153.graph sourceMap1344=true := by decide +kernel
theorem fusedMap1344_checked : acceptsGraphIso
    (fused (graph core1344) (root 9) 0 2) DegreeTwoThreeSpectrum2155.graph fusedMap1344=true := by decide +kernel
theorem certified1344 : Certified (graph core1344) (root 9) 0 2 :=
  of_native_maps core1344 DegreeTwoThreeSpectrum2153.graph DegreeTwoThreeSpectrum2155.graph
    sourceMap1344 fusedMap1344 sourceMap1344_checked fusedMap1344_checked
    DegreeTwoThreeFiniteComparisons.comparison1344
#print axioms sourceMap1344_checked
#print axioms fusedMap1344_checked
#print axioms certified1344
def sourceMap1344swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1344swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1344swap_checked : acceptsGraphIso
    (source (graph core1344) (root 9) 2 0) DegreeTwoThreeSpectrum2153.graph sourceMap1344swap=true := by decide +kernel
theorem fusedMap1344swap_checked : acceptsGraphIso
    (fused (graph core1344) (root 9) 2 0) DegreeTwoThreeSpectrum2155.graph fusedMap1344swap=true := by decide +kernel
theorem certified1344swap : Certified (graph core1344) (root 9) 2 0 :=
  of_native_maps core1344 DegreeTwoThreeSpectrum2153.graph DegreeTwoThreeSpectrum2155.graph
    sourceMap1344swap fusedMap1344swap sourceMap1344swap_checked fusedMap1344swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1344
#print axioms sourceMap1344swap_checked
#print axioms fusedMap1344swap_checked
#print axioms certified1344swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
