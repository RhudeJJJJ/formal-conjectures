/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1917 : Family 10 := level10.get ⟨1413,by decide⟩
def sourceMap1917 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,7,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap1917 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1917_checked : acceptsGraphIso
    (source (graph core1917) (root 10) 0 2) DegreeTwoThreeSpectrum3621.graph sourceMap1917=true := by decide +kernel
theorem fusedMap1917_checked : acceptsGraphIso
    (fused (graph core1917) (root 10) 0 2) DegreeTwoThreeSpectrum3633.graph fusedMap1917=true := by decide +kernel
theorem certified1917 : Certified (graph core1917) (root 10) 0 2 :=
  of_native_maps core1917 DegreeTwoThreeSpectrum3621.graph DegreeTwoThreeSpectrum3633.graph
    sourceMap1917 fusedMap1917 sourceMap1917_checked fusedMap1917_checked
    DegreeTwoThreeFiniteComparisons.comparison1917
#print axioms sourceMap1917_checked
#print axioms fusedMap1917_checked
#print axioms certified1917
def sourceMap1917swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,4,5,6,7] (sourceLabel 10 2 0 v)
def fusedMap1917swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1917swap_checked : acceptsGraphIso
    (source (graph core1917) (root 10) 2 0) DegreeTwoThreeSpectrum3621.graph sourceMap1917swap=true := by decide +kernel
theorem fusedMap1917swap_checked : acceptsGraphIso
    (fused (graph core1917) (root 10) 2 0) DegreeTwoThreeSpectrum3633.graph fusedMap1917swap=true := by decide +kernel
theorem certified1917swap : Certified (graph core1917) (root 10) 2 0 :=
  of_native_maps core1917 DegreeTwoThreeSpectrum3621.graph DegreeTwoThreeSpectrum3633.graph
    sourceMap1917swap fusedMap1917swap sourceMap1917swap_checked fusedMap1917swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1917
#print axioms sourceMap1917swap_checked
#print axioms fusedMap1917swap_checked
#print axioms certified1917swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
