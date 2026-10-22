/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1936 : Family 10 := level10.get ⟨1453,by decide⟩
def sourceMap1936 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,4,5,6,7,8,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1936 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1936_checked : acceptsGraphIso
    (source (graph core1936) (root 10) 0 2) DegreeTwoThreeSpectrum3642.graph sourceMap1936=true := by decide +kernel
theorem fusedMap1936_checked : acceptsGraphIso
    (fused (graph core1936) (root 10) 0 2) DegreeTwoThreeSpectrum3693.graph fusedMap1936=true := by decide +kernel
theorem certified1936 : Certified (graph core1936) (root 10) 0 2 :=
  of_native_maps core1936 DegreeTwoThreeSpectrum3642.graph DegreeTwoThreeSpectrum3693.graph
    sourceMap1936 fusedMap1936 sourceMap1936_checked fusedMap1936_checked
    DegreeTwoThreeFiniteComparisons.comparison1936
#print axioms sourceMap1936_checked
#print axioms fusedMap1936_checked
#print axioms certified1936
def sourceMap1936swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,4,5,6,7,1,2,3,8] (sourceLabel 10 2 0 v)
def fusedMap1936swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1936swap_checked : acceptsGraphIso
    (source (graph core1936) (root 10) 2 0) DegreeTwoThreeSpectrum3642.graph sourceMap1936swap=true := by decide +kernel
theorem fusedMap1936swap_checked : acceptsGraphIso
    (fused (graph core1936) (root 10) 2 0) DegreeTwoThreeSpectrum3693.graph fusedMap1936swap=true := by decide +kernel
theorem certified1936swap : Certified (graph core1936) (root 10) 2 0 :=
  of_native_maps core1936 DegreeTwoThreeSpectrum3642.graph DegreeTwoThreeSpectrum3693.graph
    sourceMap1936swap fusedMap1936swap sourceMap1936swap_checked fusedMap1936swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1936
#print axioms sourceMap1936swap_checked
#print axioms fusedMap1936swap_checked
#print axioms certified1936swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
