/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1764 : Family 10 := level10.get ⟨1043,by decide⟩
def sourceMap1764 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1764 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1764_checked : acceptsGraphIso
    (source (graph core1764) (root 10) 0 2) DegreeTwoThreeSpectrum3079.graph sourceMap1764=true := by decide +kernel
theorem fusedMap1764_checked : acceptsGraphIso
    (fused (graph core1764) (root 10) 0 2) DegreeTwoThreeSpectrum3081.graph fusedMap1764=true := by decide +kernel
theorem certified1764 : Certified (graph core1764) (root 10) 0 2 :=
  of_native_maps core1764 DegreeTwoThreeSpectrum3079.graph DegreeTwoThreeSpectrum3081.graph
    sourceMap1764 fusedMap1764 sourceMap1764_checked fusedMap1764_checked
    DegreeTwoThreeFiniteComparisons.comparison1764
#print axioms sourceMap1764_checked
#print axioms fusedMap1764_checked
#print axioms certified1764
def sourceMap1764swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1764swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1764swap_checked : acceptsGraphIso
    (source (graph core1764) (root 10) 2 0) DegreeTwoThreeSpectrum3079.graph sourceMap1764swap=true := by decide +kernel
theorem fusedMap1764swap_checked : acceptsGraphIso
    (fused (graph core1764) (root 10) 2 0) DegreeTwoThreeSpectrum3081.graph fusedMap1764swap=true := by decide +kernel
theorem certified1764swap : Certified (graph core1764) (root 10) 2 0 :=
  of_native_maps core1764 DegreeTwoThreeSpectrum3079.graph DegreeTwoThreeSpectrum3081.graph
    sourceMap1764swap fusedMap1764swap sourceMap1764swap_checked fusedMap1764swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1764
#print axioms sourceMap1764swap_checked
#print axioms fusedMap1764swap_checked
#print axioms certified1764swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
