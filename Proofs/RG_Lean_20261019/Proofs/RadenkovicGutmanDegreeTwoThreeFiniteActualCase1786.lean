/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1786 : Family 10 := level10.get ⟨1100,by decide⟩
def sourceMap1786 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1786 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1786_checked : acceptsGraphIso
    (source (graph core1786) (root 10) 0 2) DegreeTwoThreeSpectrum3166.graph sourceMap1786=true := by decide +kernel
theorem fusedMap1786_checked : acceptsGraphIso
    (fused (graph core1786) (root 10) 0 2) DegreeTwoThreeSpectrum3167.graph fusedMap1786=true := by decide +kernel
theorem certified1786 : Certified (graph core1786) (root 10) 0 2 :=
  of_native_maps core1786 DegreeTwoThreeSpectrum3166.graph DegreeTwoThreeSpectrum3167.graph
    sourceMap1786 fusedMap1786 sourceMap1786_checked fusedMap1786_checked
    DegreeTwoThreeFiniteComparisons.comparison1786
#print axioms sourceMap1786_checked
#print axioms fusedMap1786_checked
#print axioms certified1786
def sourceMap1786swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1786swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1786swap_checked : acceptsGraphIso
    (source (graph core1786) (root 10) 2 0) DegreeTwoThreeSpectrum3166.graph sourceMap1786swap=true := by decide +kernel
theorem fusedMap1786swap_checked : acceptsGraphIso
    (fused (graph core1786) (root 10) 2 0) DegreeTwoThreeSpectrum3167.graph fusedMap1786swap=true := by decide +kernel
theorem certified1786swap : Certified (graph core1786) (root 10) 2 0 :=
  of_native_maps core1786 DegreeTwoThreeSpectrum3166.graph DegreeTwoThreeSpectrum3167.graph
    sourceMap1786swap fusedMap1786swap sourceMap1786swap_checked fusedMap1786swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1786
#print axioms sourceMap1786swap_checked
#print axioms fusedMap1786swap_checked
#print axioms certified1786swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
