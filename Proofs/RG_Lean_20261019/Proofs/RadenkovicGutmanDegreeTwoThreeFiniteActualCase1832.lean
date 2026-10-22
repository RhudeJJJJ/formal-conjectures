/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1832 : Family 10 := level10.get ⟨1209,by decide⟩
def sourceMap1832 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1832 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1832_checked : acceptsGraphIso
    (source (graph core1832) (root 10) 0 2) DegreeTwoThreeSpectrum3331.graph sourceMap1832=true := by decide +kernel
theorem fusedMap1832_checked : acceptsGraphIso
    (fused (graph core1832) (root 10) 0 2) DegreeTwoThreeSpectrum3335.graph fusedMap1832=true := by decide +kernel
theorem certified1832 : Certified (graph core1832) (root 10) 0 2 :=
  of_native_maps core1832 DegreeTwoThreeSpectrum3331.graph DegreeTwoThreeSpectrum3335.graph
    sourceMap1832 fusedMap1832 sourceMap1832_checked fusedMap1832_checked
    DegreeTwoThreeFiniteComparisons.comparison1832
#print axioms sourceMap1832_checked
#print axioms fusedMap1832_checked
#print axioms certified1832
def sourceMap1832swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1832swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1832swap_checked : acceptsGraphIso
    (source (graph core1832) (root 10) 2 0) DegreeTwoThreeSpectrum3331.graph sourceMap1832swap=true := by decide +kernel
theorem fusedMap1832swap_checked : acceptsGraphIso
    (fused (graph core1832) (root 10) 2 0) DegreeTwoThreeSpectrum3335.graph fusedMap1832swap=true := by decide +kernel
theorem certified1832swap : Certified (graph core1832) (root 10) 2 0 :=
  of_native_maps core1832 DegreeTwoThreeSpectrum3331.graph DegreeTwoThreeSpectrum3335.graph
    sourceMap1832swap fusedMap1832swap sourceMap1832swap_checked fusedMap1832swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1832
#print axioms sourceMap1832swap_checked
#print axioms fusedMap1832swap_checked
#print axioms certified1832swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
