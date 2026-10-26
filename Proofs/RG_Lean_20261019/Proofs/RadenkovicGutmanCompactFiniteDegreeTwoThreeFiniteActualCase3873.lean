/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3873 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap3873 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3873 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3873_checked : acceptsGraphIso
    (source (graph core3873) (root 8) 1 4) DegreeTwoThreeSpectrum4503.graph sourceMap3873=true := by decide +kernel
theorem fusedMap3873_checked : acceptsGraphIso
    (fused (graph core3873) (root 8) 1 4) DegreeTwoThreeSpectrum4024.graph fusedMap3873=true := by decide +kernel
theorem certified3873 : Certified (graph core3873) (root 8) 1 4 :=
  of_native_maps core3873 DegreeTwoThreeSpectrum4503.graph DegreeTwoThreeSpectrum4024.graph
    sourceMap3873 fusedMap3873 sourceMap3873_checked fusedMap3873_checked
    DegreeTwoThreeFiniteComparisons.comparison3873
#print axioms sourceMap3873_checked
#print axioms fusedMap3873_checked
#print axioms certified3873
def sourceMap3873swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3873swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3873swap_checked : acceptsGraphIso
    (source (graph core3873) (root 8) 4 1) DegreeTwoThreeSpectrum4503.graph sourceMap3873swap=true := by decide +kernel
theorem fusedMap3873swap_checked : acceptsGraphIso
    (fused (graph core3873) (root 8) 4 1) DegreeTwoThreeSpectrum4024.graph fusedMap3873swap=true := by decide +kernel
theorem certified3873swap : Certified (graph core3873) (root 8) 4 1 :=
  of_native_maps core3873 DegreeTwoThreeSpectrum4503.graph DegreeTwoThreeSpectrum4024.graph
    sourceMap3873swap fusedMap3873swap sourceMap3873swap_checked fusedMap3873swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3873
#print axioms sourceMap3873swap_checked
#print axioms fusedMap3873swap_checked
#print axioms certified3873swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
