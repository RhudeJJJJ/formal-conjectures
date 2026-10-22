/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2844 : Family 10 := level10.get ⟨1188,by decide⟩
def sourceMap2844 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2844 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2844_checked : acceptsGraphIso
    (source (graph core2844) (root 10) 0 4) DegreeTwoThreeSpectrum6360.graph sourceMap2844=true := by decide +kernel
theorem fusedMap2844_checked : acceptsGraphIso
    (fused (graph core2844) (root 10) 0 4) DegreeTwoThreeSpectrum6361.graph fusedMap2844=true := by decide +kernel
theorem certified2844 : Certified (graph core2844) (root 10) 0 4 :=
  of_native_maps core2844 DegreeTwoThreeSpectrum6360.graph DegreeTwoThreeSpectrum6361.graph
    sourceMap2844 fusedMap2844 sourceMap2844_checked fusedMap2844_checked
    DegreeTwoThreeFiniteComparisons.comparison2844
#print axioms sourceMap2844_checked
#print axioms fusedMap2844_checked
#print axioms certified2844
def sourceMap2844swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2844swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2844swap_checked : acceptsGraphIso
    (source (graph core2844) (root 10) 4 0) DegreeTwoThreeSpectrum6360.graph sourceMap2844swap=true := by decide +kernel
theorem fusedMap2844swap_checked : acceptsGraphIso
    (fused (graph core2844) (root 10) 4 0) DegreeTwoThreeSpectrum6361.graph fusedMap2844swap=true := by decide +kernel
theorem certified2844swap : Certified (graph core2844) (root 10) 4 0 :=
  of_native_maps core2844 DegreeTwoThreeSpectrum6360.graph DegreeTwoThreeSpectrum6361.graph
    sourceMap2844swap fusedMap2844swap sourceMap2844swap_checked fusedMap2844swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2844
#print axioms sourceMap2844swap_checked
#print axioms fusedMap2844swap_checked
#print axioms certified2844swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
