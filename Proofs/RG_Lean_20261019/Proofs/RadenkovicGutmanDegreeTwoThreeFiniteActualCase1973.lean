/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1973 : Family 10 := level10.get ⟨1558,by decide⟩
def sourceMap1973 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1973 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1973_checked : acceptsGraphIso
    (source (graph core1973) (root 10) 0 2) DegreeTwoThreeSpectrum3756.graph sourceMap1973=true := by decide +kernel
theorem fusedMap1973_checked : acceptsGraphIso
    (fused (graph core1973) (root 10) 0 2) DegreeTwoThreeSpectrum3041.graph fusedMap1973=true := by decide +kernel
theorem certified1973 : Certified (graph core1973) (root 10) 0 2 :=
  of_native_maps core1973 DegreeTwoThreeSpectrum3756.graph DegreeTwoThreeSpectrum3041.graph
    sourceMap1973 fusedMap1973 sourceMap1973_checked fusedMap1973_checked
    DegreeTwoThreeFiniteComparisons.comparison1973
#print axioms sourceMap1973_checked
#print axioms fusedMap1973_checked
#print axioms certified1973
def sourceMap1973swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1973swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1973swap_checked : acceptsGraphIso
    (source (graph core1973) (root 10) 2 0) DegreeTwoThreeSpectrum3756.graph sourceMap1973swap=true := by decide +kernel
theorem fusedMap1973swap_checked : acceptsGraphIso
    (fused (graph core1973) (root 10) 2 0) DegreeTwoThreeSpectrum3041.graph fusedMap1973swap=true := by decide +kernel
theorem certified1973swap : Certified (graph core1973) (root 10) 2 0 :=
  of_native_maps core1973 DegreeTwoThreeSpectrum3756.graph DegreeTwoThreeSpectrum3041.graph
    sourceMap1973swap fusedMap1973swap sourceMap1973swap_checked fusedMap1973swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1973
#print axioms sourceMap1973swap_checked
#print axioms fusedMap1973swap_checked
#print axioms certified1973swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
