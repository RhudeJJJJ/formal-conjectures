/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1790 : Family 10 := level10.get ⟨1111,by decide⟩
def sourceMap1790 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1790 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1790_checked : acceptsGraphIso
    (source (graph core1790) (root 10) 0 2) DegreeTwoThreeSpectrum3182.graph sourceMap1790=true := by decide +kernel
theorem fusedMap1790_checked : acceptsGraphIso
    (fused (graph core1790) (root 10) 0 2) DegreeTwoThreeSpectrum3183.graph fusedMap1790=true := by decide +kernel
theorem certified1790 : Certified (graph core1790) (root 10) 0 2 :=
  of_native_maps core1790 DegreeTwoThreeSpectrum3182.graph DegreeTwoThreeSpectrum3183.graph
    sourceMap1790 fusedMap1790 sourceMap1790_checked fusedMap1790_checked
    DegreeTwoThreeFiniteComparisons.comparison1790
#print axioms sourceMap1790_checked
#print axioms fusedMap1790_checked
#print axioms certified1790
def sourceMap1790swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1790swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1790swap_checked : acceptsGraphIso
    (source (graph core1790) (root 10) 2 0) DegreeTwoThreeSpectrum3182.graph sourceMap1790swap=true := by decide +kernel
theorem fusedMap1790swap_checked : acceptsGraphIso
    (fused (graph core1790) (root 10) 2 0) DegreeTwoThreeSpectrum3183.graph fusedMap1790swap=true := by decide +kernel
theorem certified1790swap : Certified (graph core1790) (root 10) 2 0 :=
  of_native_maps core1790 DegreeTwoThreeSpectrum3182.graph DegreeTwoThreeSpectrum3183.graph
    sourceMap1790swap fusedMap1790swap sourceMap1790swap_checked fusedMap1790swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1790
#print axioms sourceMap1790swap_checked
#print axioms fusedMap1790swap_checked
#print axioms certified1790swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
