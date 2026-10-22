/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1986 : Family 10 := level10.get ⟨1587,by decide⟩
def sourceMap1986 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1986 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1986_checked : acceptsGraphIso
    (source (graph core1986) (root 10) 0 2) DegreeTwoThreeSpectrum3770.graph sourceMap1986=true := by decide +kernel
theorem fusedMap1986_checked : acceptsGraphIso
    (fused (graph core1986) (root 10) 0 2) DegreeTwoThreeSpectrum3086.graph fusedMap1986=true := by decide +kernel
theorem certified1986 : Certified (graph core1986) (root 10) 0 2 :=
  of_native_maps core1986 DegreeTwoThreeSpectrum3770.graph DegreeTwoThreeSpectrum3086.graph
    sourceMap1986 fusedMap1986 sourceMap1986_checked fusedMap1986_checked
    DegreeTwoThreeFiniteComparisons.comparison1986
#print axioms sourceMap1986_checked
#print axioms fusedMap1986_checked
#print axioms certified1986
def sourceMap1986swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1986swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1986swap_checked : acceptsGraphIso
    (source (graph core1986) (root 10) 2 0) DegreeTwoThreeSpectrum3770.graph sourceMap1986swap=true := by decide +kernel
theorem fusedMap1986swap_checked : acceptsGraphIso
    (fused (graph core1986) (root 10) 2 0) DegreeTwoThreeSpectrum3086.graph fusedMap1986swap=true := by decide +kernel
theorem certified1986swap : Certified (graph core1986) (root 10) 2 0 :=
  of_native_maps core1986 DegreeTwoThreeSpectrum3770.graph DegreeTwoThreeSpectrum3086.graph
    sourceMap1986swap fusedMap1986swap sourceMap1986swap_checked fusedMap1986swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1986
#print axioms sourceMap1986swap_checked
#print axioms fusedMap1986swap_checked
#print axioms certified1986swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
