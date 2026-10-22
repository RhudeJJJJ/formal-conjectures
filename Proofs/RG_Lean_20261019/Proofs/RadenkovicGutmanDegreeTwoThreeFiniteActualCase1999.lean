/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1999 : Family 10 := level10.get ⟨1621,by decide⟩
def sourceMap1999 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1999 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1999_checked : acceptsGraphIso
    (source (graph core1999) (root 10) 0 2) DegreeTwoThreeSpectrum3786.graph sourceMap1999=true := by decide +kernel
theorem fusedMap1999_checked : acceptsGraphIso
    (fused (graph core1999) (root 10) 0 2) DegreeTwoThreeSpectrum3163.graph fusedMap1999=true := by decide +kernel
theorem certified1999 : Certified (graph core1999) (root 10) 0 2 :=
  of_native_maps core1999 DegreeTwoThreeSpectrum3786.graph DegreeTwoThreeSpectrum3163.graph
    sourceMap1999 fusedMap1999 sourceMap1999_checked fusedMap1999_checked
    DegreeTwoThreeFiniteComparisons.comparison1999
#print axioms sourceMap1999_checked
#print axioms fusedMap1999_checked
#print axioms certified1999
def sourceMap1999swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1999swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1999swap_checked : acceptsGraphIso
    (source (graph core1999) (root 10) 2 0) DegreeTwoThreeSpectrum3786.graph sourceMap1999swap=true := by decide +kernel
theorem fusedMap1999swap_checked : acceptsGraphIso
    (fused (graph core1999) (root 10) 2 0) DegreeTwoThreeSpectrum3163.graph fusedMap1999swap=true := by decide +kernel
theorem certified1999swap : Certified (graph core1999) (root 10) 2 0 :=
  of_native_maps core1999 DegreeTwoThreeSpectrum3786.graph DegreeTwoThreeSpectrum3163.graph
    sourceMap1999swap fusedMap1999swap sourceMap1999swap_checked fusedMap1999swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1999
#print axioms sourceMap1999swap_checked
#print axioms fusedMap1999swap_checked
#print axioms certified1999swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
