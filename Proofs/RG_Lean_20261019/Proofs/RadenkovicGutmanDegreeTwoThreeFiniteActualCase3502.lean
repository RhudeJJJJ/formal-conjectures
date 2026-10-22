/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3502 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap3502 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3502 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3502_checked : acceptsGraphIso
    (source (graph core3502) (root 7) 0 6) DegreeTwoThreeSpectrum3889.graph sourceMap3502=true := by decide +kernel
theorem fusedMap3502_checked : acceptsGraphIso
    (fused (graph core3502) (root 7) 0 6) DegreeTwoThreeSpectrum3891.graph fusedMap3502=true := by decide +kernel
theorem certified3502 : Certified (graph core3502) (root 7) 0 6 :=
  of_native_maps core3502 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap3502 fusedMap3502 sourceMap3502_checked fusedMap3502_checked
    DegreeTwoThreeFiniteComparisons.comparison3502
#print axioms sourceMap3502_checked
#print axioms fusedMap3502_checked
#print axioms certified3502
def sourceMap3502swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,15,8] (sourceLabel 7 6 0 v)
def fusedMap3502swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3502swap_checked : acceptsGraphIso
    (source (graph core3502) (root 7) 6 0) DegreeTwoThreeSpectrum3889.graph sourceMap3502swap=true := by decide +kernel
theorem fusedMap3502swap_checked : acceptsGraphIso
    (fused (graph core3502) (root 7) 6 0) DegreeTwoThreeSpectrum3891.graph fusedMap3502swap=true := by decide +kernel
theorem certified3502swap : Certified (graph core3502) (root 7) 6 0 :=
  of_native_maps core3502 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap3502swap fusedMap3502swap sourceMap3502swap_checked fusedMap3502swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3502
#print axioms sourceMap3502swap_checked
#print axioms fusedMap3502swap_checked
#print axioms certified3502swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
