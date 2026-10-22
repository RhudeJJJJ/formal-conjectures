/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1194 : Family 9 := level9.get ⟨22,by decide⟩
def sourceMap1194 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1194 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1194_checked : acceptsGraphIso
    (source (graph core1194) (root 9) 0 2) DegreeTwoThreeSpectrum1853.graph sourceMap1194=true := by decide +kernel
theorem fusedMap1194_checked : acceptsGraphIso
    (fused (graph core1194) (root 9) 0 2) DegreeTwoThreeSpectrum1721.graph fusedMap1194=true := by decide +kernel
theorem certified1194 : Certified (graph core1194) (root 9) 0 2 :=
  of_native_maps core1194 DegreeTwoThreeSpectrum1853.graph DegreeTwoThreeSpectrum1721.graph
    sourceMap1194 fusedMap1194 sourceMap1194_checked fusedMap1194_checked
    DegreeTwoThreeFiniteComparisons.comparison1194
#print axioms sourceMap1194_checked
#print axioms fusedMap1194_checked
#print axioms certified1194
def sourceMap1194swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1194swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1194swap_checked : acceptsGraphIso
    (source (graph core1194) (root 9) 2 0) DegreeTwoThreeSpectrum1853.graph sourceMap1194swap=true := by decide +kernel
theorem fusedMap1194swap_checked : acceptsGraphIso
    (fused (graph core1194) (root 9) 2 0) DegreeTwoThreeSpectrum1721.graph fusedMap1194swap=true := by decide +kernel
theorem certified1194swap : Certified (graph core1194) (root 9) 2 0 :=
  of_native_maps core1194 DegreeTwoThreeSpectrum1853.graph DegreeTwoThreeSpectrum1721.graph
    sourceMap1194swap fusedMap1194swap sourceMap1194swap_checked fusedMap1194swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1194
#print axioms sourceMap1194swap_checked
#print axioms fusedMap1194swap_checked
#print axioms certified1194swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
