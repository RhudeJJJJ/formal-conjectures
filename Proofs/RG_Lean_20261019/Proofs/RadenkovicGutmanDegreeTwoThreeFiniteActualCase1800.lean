/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1800 : Family 10 := level10.get ⟨1137,by decide⟩
def sourceMap1800 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1800 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1800_checked : acceptsGraphIso
    (source (graph core1800) (root 10) 0 2) DegreeTwoThreeSpectrum3222.graph sourceMap1800=true := by decide +kernel
theorem fusedMap1800_checked : acceptsGraphIso
    (fused (graph core1800) (root 10) 0 2) DegreeTwoThreeSpectrum3223.graph fusedMap1800=true := by decide +kernel
theorem certified1800 : Certified (graph core1800) (root 10) 0 2 :=
  of_native_maps core1800 DegreeTwoThreeSpectrum3222.graph DegreeTwoThreeSpectrum3223.graph
    sourceMap1800 fusedMap1800 sourceMap1800_checked fusedMap1800_checked
    DegreeTwoThreeFiniteComparisons.comparison1800
#print axioms sourceMap1800_checked
#print axioms fusedMap1800_checked
#print axioms certified1800
def sourceMap1800swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1800swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1800swap_checked : acceptsGraphIso
    (source (graph core1800) (root 10) 2 0) DegreeTwoThreeSpectrum3222.graph sourceMap1800swap=true := by decide +kernel
theorem fusedMap1800swap_checked : acceptsGraphIso
    (fused (graph core1800) (root 10) 2 0) DegreeTwoThreeSpectrum3223.graph fusedMap1800swap=true := by decide +kernel
theorem certified1800swap : Certified (graph core1800) (root 10) 2 0 :=
  of_native_maps core1800 DegreeTwoThreeSpectrum3222.graph DegreeTwoThreeSpectrum3223.graph
    sourceMap1800swap fusedMap1800swap sourceMap1800swap_checked fusedMap1800swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1800
#print axioms sourceMap1800swap_checked
#print axioms fusedMap1800swap_checked
#print axioms certified1800swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
