/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3072 : Family 10 := level10.get ⟨1802,by decide⟩
def sourceMap3072 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3072 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3072_checked : acceptsGraphIso
    (source (graph core3072) (root 10) 0 4) DegreeTwoThreeSpectrum7059.graph sourceMap3072=true := by decide +kernel
theorem fusedMap3072_checked : acceptsGraphIso
    (fused (graph core3072) (root 10) 0 4) DegreeTwoThreeSpectrum7060.graph fusedMap3072=true := by decide +kernel
theorem certified3072 : Certified (graph core3072) (root 10) 0 4 :=
  of_native_maps core3072 DegreeTwoThreeSpectrum7059.graph DegreeTwoThreeSpectrum7060.graph
    sourceMap3072 fusedMap3072 sourceMap3072_checked fusedMap3072_checked
    DegreeTwoThreeFiniteComparisons.comparison3072
#print axioms sourceMap3072_checked
#print axioms fusedMap3072_checked
#print axioms certified3072
def sourceMap3072swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3072swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3072swap_checked : acceptsGraphIso
    (source (graph core3072) (root 10) 4 0) DegreeTwoThreeSpectrum7059.graph sourceMap3072swap=true := by decide +kernel
theorem fusedMap3072swap_checked : acceptsGraphIso
    (fused (graph core3072) (root 10) 4 0) DegreeTwoThreeSpectrum7060.graph fusedMap3072swap=true := by decide +kernel
theorem certified3072swap : Certified (graph core3072) (root 10) 4 0 :=
  of_native_maps core3072 DegreeTwoThreeSpectrum7059.graph DegreeTwoThreeSpectrum7060.graph
    sourceMap3072swap fusedMap3072swap sourceMap3072swap_checked fusedMap3072swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3072
#print axioms sourceMap3072swap_checked
#print axioms fusedMap3072swap_checked
#print axioms certified3072swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
