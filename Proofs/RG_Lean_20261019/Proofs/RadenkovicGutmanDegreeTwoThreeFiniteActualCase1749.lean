/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1749 : Family 10 := level10.get ⟨1002,by decide⟩
def sourceMap1749 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1749 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1749_checked : acceptsGraphIso
    (source (graph core1749) (root 10) 0 2) DegreeTwoThreeSpectrum3010.graph sourceMap1749=true := by decide +kernel
theorem fusedMap1749_checked : acceptsGraphIso
    (fused (graph core1749) (root 10) 0 2) DegreeTwoThreeSpectrum3011.graph fusedMap1749=true := by decide +kernel
theorem certified1749 : Certified (graph core1749) (root 10) 0 2 :=
  of_native_maps core1749 DegreeTwoThreeSpectrum3010.graph DegreeTwoThreeSpectrum3011.graph
    sourceMap1749 fusedMap1749 sourceMap1749_checked fusedMap1749_checked
    DegreeTwoThreeFiniteComparisons.comparison1749
#print axioms sourceMap1749_checked
#print axioms fusedMap1749_checked
#print axioms certified1749
def sourceMap1749swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1749swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1749swap_checked : acceptsGraphIso
    (source (graph core1749) (root 10) 2 0) DegreeTwoThreeSpectrum3010.graph sourceMap1749swap=true := by decide +kernel
theorem fusedMap1749swap_checked : acceptsGraphIso
    (fused (graph core1749) (root 10) 2 0) DegreeTwoThreeSpectrum3011.graph fusedMap1749swap=true := by decide +kernel
theorem certified1749swap : Certified (graph core1749) (root 10) 2 0 :=
  of_native_maps core1749 DegreeTwoThreeSpectrum3010.graph DegreeTwoThreeSpectrum3011.graph
    sourceMap1749swap fusedMap1749swap sourceMap1749swap_checked fusedMap1749swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1749
#print axioms sourceMap1749swap_checked
#print axioms fusedMap1749swap_checked
#print axioms certified1749swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
