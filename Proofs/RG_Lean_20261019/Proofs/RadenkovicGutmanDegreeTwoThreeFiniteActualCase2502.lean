/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2502 : Family 10 := level10.get ⟨213,by decide⟩
def sourceMap2502 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2502 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2502_checked : acceptsGraphIso
    (source (graph core2502) (root 10) 0 4) DegreeTwoThreeSpectrum5220.graph sourceMap2502=true := by decide +kernel
theorem fusedMap2502_checked : acceptsGraphIso
    (fused (graph core2502) (root 10) 0 4) DegreeTwoThreeSpectrum5222.graph fusedMap2502=true := by decide +kernel
theorem certified2502 : Certified (graph core2502) (root 10) 0 4 :=
  of_native_maps core2502 DegreeTwoThreeSpectrum5220.graph DegreeTwoThreeSpectrum5222.graph
    sourceMap2502 fusedMap2502 sourceMap2502_checked fusedMap2502_checked
    DegreeTwoThreeFiniteComparisons.comparison2502
#print axioms sourceMap2502_checked
#print axioms fusedMap2502_checked
#print axioms certified2502
def sourceMap2502swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2502swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2502swap_checked : acceptsGraphIso
    (source (graph core2502) (root 10) 4 0) DegreeTwoThreeSpectrum5220.graph sourceMap2502swap=true := by decide +kernel
theorem fusedMap2502swap_checked : acceptsGraphIso
    (fused (graph core2502) (root 10) 4 0) DegreeTwoThreeSpectrum5222.graph fusedMap2502swap=true := by decide +kernel
theorem certified2502swap : Certified (graph core2502) (root 10) 4 0 :=
  of_native_maps core2502 DegreeTwoThreeSpectrum5220.graph DegreeTwoThreeSpectrum5222.graph
    sourceMap2502swap fusedMap2502swap sourceMap2502swap_checked fusedMap2502swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2502
#print axioms sourceMap2502swap_checked
#print axioms fusedMap2502swap_checked
#print axioms certified2502swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
