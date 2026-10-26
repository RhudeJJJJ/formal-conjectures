/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3841 : Family 8 := level8.get ⟨64,by decide⟩
def sourceMap3841 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3841 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3841_checked : acceptsGraphIso
    (source (graph core3841) (root 8) 1 4) DegreeTwoThreeSpectrum4515.graph sourceMap3841=true := by decide +kernel
theorem fusedMap3841_checked : acceptsGraphIso
    (fused (graph core3841) (root 8) 1 4) DegreeTwoThreeSpectrum4033.graph fusedMap3841=true := by decide +kernel
theorem certified3841 : Certified (graph core3841) (root 8) 1 4 :=
  of_native_maps core3841 DegreeTwoThreeSpectrum4515.graph DegreeTwoThreeSpectrum4033.graph
    sourceMap3841 fusedMap3841 sourceMap3841_checked fusedMap3841_checked
    DegreeTwoThreeFiniteComparisons.comparison3841
#print axioms sourceMap3841_checked
#print axioms fusedMap3841_checked
#print axioms certified3841
def sourceMap3841swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3841swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3841swap_checked : acceptsGraphIso
    (source (graph core3841) (root 8) 4 1) DegreeTwoThreeSpectrum4515.graph sourceMap3841swap=true := by decide +kernel
theorem fusedMap3841swap_checked : acceptsGraphIso
    (fused (graph core3841) (root 8) 4 1) DegreeTwoThreeSpectrum4033.graph fusedMap3841swap=true := by decide +kernel
theorem certified3841swap : Certified (graph core3841) (root 8) 4 1 :=
  of_native_maps core3841 DegreeTwoThreeSpectrum4515.graph DegreeTwoThreeSpectrum4033.graph
    sourceMap3841swap fusedMap3841swap sourceMap3841swap_checked fusedMap3841swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3841
#print axioms sourceMap3841swap_checked
#print axioms fusedMap3841swap_checked
#print axioms certified3841swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
