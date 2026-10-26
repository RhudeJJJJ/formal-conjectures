/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3861 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap3861 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3861 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3861_checked : acceptsGraphIso
    (source (graph core3861) (root 8) 1 4) DegreeTwoThreeSpectrum4349.graph sourceMap3861=true := by decide +kernel
theorem fusedMap3861_checked : acceptsGraphIso
    (fused (graph core3861) (root 8) 1 4) DegreeTwoThreeSpectrum3944.graph fusedMap3861=true := by decide +kernel
theorem certified3861 : Certified (graph core3861) (root 8) 1 4 :=
  of_native_maps core3861 DegreeTwoThreeSpectrum4349.graph DegreeTwoThreeSpectrum3944.graph
    sourceMap3861 fusedMap3861 sourceMap3861_checked fusedMap3861_checked
    DegreeTwoThreeFiniteComparisons.comparison3861
#print axioms sourceMap3861_checked
#print axioms fusedMap3861_checked
#print axioms certified3861
def sourceMap3861swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3861swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3861swap_checked : acceptsGraphIso
    (source (graph core3861) (root 8) 4 1) DegreeTwoThreeSpectrum4349.graph sourceMap3861swap=true := by decide +kernel
theorem fusedMap3861swap_checked : acceptsGraphIso
    (fused (graph core3861) (root 8) 4 1) DegreeTwoThreeSpectrum3944.graph fusedMap3861swap=true := by decide +kernel
theorem certified3861swap : Certified (graph core3861) (root 8) 4 1 :=
  of_native_maps core3861 DegreeTwoThreeSpectrum4349.graph DegreeTwoThreeSpectrum3944.graph
    sourceMap3861swap fusedMap3861swap sourceMap3861swap_checked fusedMap3861swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3861
#print axioms sourceMap3861swap_checked
#print axioms fusedMap3861swap_checked
#print axioms certified3861swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
