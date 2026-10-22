/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1869 : Family 10 := level10.get ⟨1302,by decide⟩
def sourceMap1869 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1869 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1869_checked : acceptsGraphIso
    (source (graph core1869) (root 10) 0 2) DegreeTwoThreeSpectrum3466.graph sourceMap1869=true := by decide +kernel
theorem fusedMap1869_checked : acceptsGraphIso
    (fused (graph core1869) (root 10) 0 2) DegreeTwoThreeSpectrum3467.graph fusedMap1869=true := by decide +kernel
theorem certified1869 : Certified (graph core1869) (root 10) 0 2 :=
  of_native_maps core1869 DegreeTwoThreeSpectrum3466.graph DegreeTwoThreeSpectrum3467.graph
    sourceMap1869 fusedMap1869 sourceMap1869_checked fusedMap1869_checked
    DegreeTwoThreeFiniteComparisons.comparison1869
#print axioms sourceMap1869_checked
#print axioms fusedMap1869_checked
#print axioms certified1869
def sourceMap1869swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1869swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1869swap_checked : acceptsGraphIso
    (source (graph core1869) (root 10) 2 0) DegreeTwoThreeSpectrum3466.graph sourceMap1869swap=true := by decide +kernel
theorem fusedMap1869swap_checked : acceptsGraphIso
    (fused (graph core1869) (root 10) 2 0) DegreeTwoThreeSpectrum3467.graph fusedMap1869swap=true := by decide +kernel
theorem certified1869swap : Certified (graph core1869) (root 10) 2 0 :=
  of_native_maps core1869 DegreeTwoThreeSpectrum3466.graph DegreeTwoThreeSpectrum3467.graph
    sourceMap1869swap fusedMap1869swap sourceMap1869swap_checked fusedMap1869swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1869
#print axioms sourceMap1869swap_checked
#print axioms fusedMap1869swap_checked
#print axioms certified1869swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
