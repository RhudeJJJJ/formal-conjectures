/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2972 : Family 10 := level10.get ⟨1481,by decide⟩
def sourceMap2972 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2972 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2972_checked : acceptsGraphIso
    (source (graph core2972) (root 10) 0 4) DegreeTwoThreeSpectrum6970.graph sourceMap2972=true := by decide +kernel
theorem fusedMap2972_checked : acceptsGraphIso
    (fused (graph core2972) (root 10) 0 4) DegreeTwoThreeSpectrum6971.graph fusedMap2972=true := by decide +kernel
theorem certified2972 : Certified (graph core2972) (root 10) 0 4 :=
  of_native_maps core2972 DegreeTwoThreeSpectrum6970.graph DegreeTwoThreeSpectrum6971.graph
    sourceMap2972 fusedMap2972 sourceMap2972_checked fusedMap2972_checked
    DegreeTwoThreeFiniteComparisons.comparison2972
#print axioms sourceMap2972_checked
#print axioms fusedMap2972_checked
#print axioms certified2972
def sourceMap2972swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2972swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2972swap_checked : acceptsGraphIso
    (source (graph core2972) (root 10) 4 0) DegreeTwoThreeSpectrum6970.graph sourceMap2972swap=true := by decide +kernel
theorem fusedMap2972swap_checked : acceptsGraphIso
    (fused (graph core2972) (root 10) 4 0) DegreeTwoThreeSpectrum6971.graph fusedMap2972swap=true := by decide +kernel
theorem certified2972swap : Certified (graph core2972) (root 10) 4 0 :=
  of_native_maps core2972 DegreeTwoThreeSpectrum6970.graph DegreeTwoThreeSpectrum6971.graph
    sourceMap2972swap fusedMap2972swap sourceMap2972swap_checked fusedMap2972swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2972
#print axioms sourceMap2972swap_checked
#print axioms fusedMap2972swap_checked
#print axioms certified2972swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
