/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1952 : Family 10 := level10.get ⟨1495,by decide⟩
def sourceMap1952 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1952 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1952_checked : acceptsGraphIso
    (source (graph core1952) (root 10) 0 2) DegreeTwoThreeSpectrum3096.graph sourceMap1952=true := by decide +kernel
theorem fusedMap1952_checked : acceptsGraphIso
    (fused (graph core1952) (root 10) 0 2) DegreeTwoThreeSpectrum3724.graph fusedMap1952=true := by decide +kernel
theorem certified1952 : Certified (graph core1952) (root 10) 0 2 :=
  of_native_maps core1952 DegreeTwoThreeSpectrum3096.graph DegreeTwoThreeSpectrum3724.graph
    sourceMap1952 fusedMap1952 sourceMap1952_checked fusedMap1952_checked
    DegreeTwoThreeFiniteComparisons.comparison1952
#print axioms sourceMap1952_checked
#print axioms fusedMap1952_checked
#print axioms certified1952
def sourceMap1952swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1952swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1952swap_checked : acceptsGraphIso
    (source (graph core1952) (root 10) 2 0) DegreeTwoThreeSpectrum3096.graph sourceMap1952swap=true := by decide +kernel
theorem fusedMap1952swap_checked : acceptsGraphIso
    (fused (graph core1952) (root 10) 2 0) DegreeTwoThreeSpectrum3724.graph fusedMap1952swap=true := by decide +kernel
theorem certified1952swap : Certified (graph core1952) (root 10) 2 0 :=
  of_native_maps core1952 DegreeTwoThreeSpectrum3096.graph DegreeTwoThreeSpectrum3724.graph
    sourceMap1952swap fusedMap1952swap sourceMap1952swap_checked fusedMap1952swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1952
#print axioms sourceMap1952swap_checked
#print axioms fusedMap1952swap_checked
#print axioms certified1952swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
