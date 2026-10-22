/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2828 : Family 10 := level10.get ⟨1149,by decide⟩
def sourceMap2828 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2828 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2828_checked : acceptsGraphIso
    (source (graph core2828) (root 10) 0 4) DegreeTwoThreeSpectrum6287.graph sourceMap2828=true := by decide +kernel
theorem fusedMap2828_checked : acceptsGraphIso
    (fused (graph core2828) (root 10) 0 4) DegreeTwoThreeSpectrum6288.graph fusedMap2828=true := by decide +kernel
theorem certified2828 : Certified (graph core2828) (root 10) 0 4 :=
  of_native_maps core2828 DegreeTwoThreeSpectrum6287.graph DegreeTwoThreeSpectrum6288.graph
    sourceMap2828 fusedMap2828 sourceMap2828_checked fusedMap2828_checked
    DegreeTwoThreeFiniteComparisons.comparison2828
#print axioms sourceMap2828_checked
#print axioms fusedMap2828_checked
#print axioms certified2828
def sourceMap2828swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2828swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2828swap_checked : acceptsGraphIso
    (source (graph core2828) (root 10) 4 0) DegreeTwoThreeSpectrum6287.graph sourceMap2828swap=true := by decide +kernel
theorem fusedMap2828swap_checked : acceptsGraphIso
    (fused (graph core2828) (root 10) 4 0) DegreeTwoThreeSpectrum6288.graph fusedMap2828swap=true := by decide +kernel
theorem certified2828swap : Certified (graph core2828) (root 10) 4 0 :=
  of_native_maps core2828 DegreeTwoThreeSpectrum6287.graph DegreeTwoThreeSpectrum6288.graph
    sourceMap2828swap fusedMap2828swap sourceMap2828swap_checked fusedMap2828swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2828
#print axioms sourceMap2828swap_checked
#print axioms fusedMap2828swap_checked
#print axioms certified2828swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
