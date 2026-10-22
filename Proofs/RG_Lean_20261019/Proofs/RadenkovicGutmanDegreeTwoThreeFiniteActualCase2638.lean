/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2638 : Family 10 := level10.get ⟨647,by decide⟩
def sourceMap2638 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2638 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2638_checked : acceptsGraphIso
    (source (graph core2638) (root 10) 0 4) DegreeTwoThreeSpectrum6412.graph sourceMap2638=true := by decide +kernel
theorem fusedMap2638_checked : acceptsGraphIso
    (fused (graph core2638) (root 10) 0 4) DegreeTwoThreeSpectrum5346.graph fusedMap2638=true := by decide +kernel
theorem certified2638 : Certified (graph core2638) (root 10) 0 4 :=
  of_native_maps core2638 DegreeTwoThreeSpectrum6412.graph DegreeTwoThreeSpectrum5346.graph
    sourceMap2638 fusedMap2638 sourceMap2638_checked fusedMap2638_checked
    DegreeTwoThreeFiniteComparisons.comparison2638
#print axioms sourceMap2638_checked
#print axioms fusedMap2638_checked
#print axioms certified2638
def sourceMap2638swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2638swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2638swap_checked : acceptsGraphIso
    (source (graph core2638) (root 10) 4 0) DegreeTwoThreeSpectrum6412.graph sourceMap2638swap=true := by decide +kernel
theorem fusedMap2638swap_checked : acceptsGraphIso
    (fused (graph core2638) (root 10) 4 0) DegreeTwoThreeSpectrum5346.graph fusedMap2638swap=true := by decide +kernel
theorem certified2638swap : Certified (graph core2638) (root 10) 4 0 :=
  of_native_maps core2638 DegreeTwoThreeSpectrum6412.graph DegreeTwoThreeSpectrum5346.graph
    sourceMap2638swap fusedMap2638swap sourceMap2638swap_checked fusedMap2638swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2638
#print axioms sourceMap2638swap_checked
#print axioms fusedMap2638swap_checked
#print axioms certified2638swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
