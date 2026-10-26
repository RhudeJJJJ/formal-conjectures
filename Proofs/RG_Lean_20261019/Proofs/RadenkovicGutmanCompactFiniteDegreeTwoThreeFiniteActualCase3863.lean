/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3863 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap3863 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3863 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3863_checked : acceptsGraphIso
    (source (graph core3863) (root 8) 1 4) DegreeTwoThreeSpectrum4363.graph sourceMap3863=true := by decide +kernel
theorem fusedMap3863_checked : acceptsGraphIso
    (fused (graph core3863) (root 8) 1 4) DegreeTwoThreeSpectrum3950.graph fusedMap3863=true := by decide +kernel
theorem certified3863 : Certified (graph core3863) (root 8) 1 4 :=
  of_native_maps core3863 DegreeTwoThreeSpectrum4363.graph DegreeTwoThreeSpectrum3950.graph
    sourceMap3863 fusedMap3863 sourceMap3863_checked fusedMap3863_checked
    DegreeTwoThreeFiniteComparisons.comparison3863
#print axioms sourceMap3863_checked
#print axioms fusedMap3863_checked
#print axioms certified3863
def sourceMap3863swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3863swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3863swap_checked : acceptsGraphIso
    (source (graph core3863) (root 8) 4 1) DegreeTwoThreeSpectrum4363.graph sourceMap3863swap=true := by decide +kernel
theorem fusedMap3863swap_checked : acceptsGraphIso
    (fused (graph core3863) (root 8) 4 1) DegreeTwoThreeSpectrum3950.graph fusedMap3863swap=true := by decide +kernel
theorem certified3863swap : Certified (graph core3863) (root 8) 4 1 :=
  of_native_maps core3863 DegreeTwoThreeSpectrum4363.graph DegreeTwoThreeSpectrum3950.graph
    sourceMap3863swap fusedMap3863swap sourceMap3863swap_checked fusedMap3863swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3863
#print axioms sourceMap3863swap_checked
#print axioms fusedMap3863swap_checked
#print axioms certified3863swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
