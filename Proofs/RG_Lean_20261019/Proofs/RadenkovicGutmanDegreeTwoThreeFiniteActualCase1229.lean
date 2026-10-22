/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1229 : Family 9 := level9.get ⟨153,by decide⟩
def sourceMap1229 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1229 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1229_checked : acceptsGraphIso
    (source (graph core1229) (root 9) 0 2) DegreeTwoThreeSpectrum1984.graph sourceMap1229=true := by decide +kernel
theorem fusedMap1229_checked : acceptsGraphIso
    (fused (graph core1229) (root 9) 0 2) DegreeTwoThreeSpectrum1752.graph fusedMap1229=true := by decide +kernel
theorem certified1229 : Certified (graph core1229) (root 9) 0 2 :=
  of_native_maps core1229 DegreeTwoThreeSpectrum1984.graph DegreeTwoThreeSpectrum1752.graph
    sourceMap1229 fusedMap1229 sourceMap1229_checked fusedMap1229_checked
    DegreeTwoThreeFiniteComparisons.comparison1229
#print axioms sourceMap1229_checked
#print axioms fusedMap1229_checked
#print axioms certified1229
def sourceMap1229swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1229swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1229swap_checked : acceptsGraphIso
    (source (graph core1229) (root 9) 2 0) DegreeTwoThreeSpectrum1984.graph sourceMap1229swap=true := by decide +kernel
theorem fusedMap1229swap_checked : acceptsGraphIso
    (fused (graph core1229) (root 9) 2 0) DegreeTwoThreeSpectrum1752.graph fusedMap1229swap=true := by decide +kernel
theorem certified1229swap : Certified (graph core1229) (root 9) 2 0 :=
  of_native_maps core1229 DegreeTwoThreeSpectrum1984.graph DegreeTwoThreeSpectrum1752.graph
    sourceMap1229swap fusedMap1229swap sourceMap1229swap_checked fusedMap1229swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1229
#print axioms sourceMap1229swap_checked
#print axioms fusedMap1229swap_checked
#print axioms certified1229swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
