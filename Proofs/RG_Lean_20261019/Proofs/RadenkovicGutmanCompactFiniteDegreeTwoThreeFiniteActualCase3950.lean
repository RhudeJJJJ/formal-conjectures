/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3950 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap3950 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,13,14,7,8,9,10,11,12] (sourceLabel 7 1 5 v)
def fusedMap3950 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3950_checked : acceptsGraphIso
    (source (graph core3950) (root 7) 1 5) DegreeTwoThreeSpectrum4170.graph sourceMap3950=true := by decide +kernel
theorem fusedMap3950_checked : acceptsGraphIso
    (fused (graph core3950) (root 7) 1 5) DegreeTwoThreeSpectrum3891.graph fusedMap3950=true := by decide +kernel
theorem certified3950 : Certified (graph core3950) (root 7) 1 5 :=
  of_native_maps core3950 DegreeTwoThreeSpectrum4170.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap3950 fusedMap3950 sourceMap3950_checked fusedMap3950_checked
    DegreeTwoThreeFiniteComparisons.comparison3950
#print axioms sourceMap3950_checked
#print axioms fusedMap3950_checked
#print axioms certified3950
def sourceMap3950swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,7,8,9,10,11,12,13,14] (sourceLabel 7 5 1 v)
def fusedMap3950swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3950swap_checked : acceptsGraphIso
    (source (graph core3950) (root 7) 5 1) DegreeTwoThreeSpectrum4170.graph sourceMap3950swap=true := by decide +kernel
theorem fusedMap3950swap_checked : acceptsGraphIso
    (fused (graph core3950) (root 7) 5 1) DegreeTwoThreeSpectrum3891.graph fusedMap3950swap=true := by decide +kernel
theorem certified3950swap : Certified (graph core3950) (root 7) 5 1 :=
  of_native_maps core3950 DegreeTwoThreeSpectrum4170.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap3950swap fusedMap3950swap sourceMap3950swap_checked fusedMap3950swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3950
#print axioms sourceMap3950swap_checked
#print axioms fusedMap3950swap_checked
#print axioms certified3950swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
