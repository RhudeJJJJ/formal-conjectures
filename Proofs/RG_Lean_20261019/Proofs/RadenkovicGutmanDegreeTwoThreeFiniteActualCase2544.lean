/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2544 : Family 10 := level10.get ⟨361,by decide⟩
def sourceMap2544 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2544 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2544_checked : acceptsGraphIso
    (source (graph core2544) (root 10) 0 4) DegreeTwoThreeSpectrum5643.graph sourceMap2544=true := by decide +kernel
theorem fusedMap2544_checked : acceptsGraphIso
    (fused (graph core2544) (root 10) 0 4) DegreeTwoThreeSpectrum5645.graph fusedMap2544=true := by decide +kernel
theorem certified2544 : Certified (graph core2544) (root 10) 0 4 :=
  of_native_maps core2544 DegreeTwoThreeSpectrum5643.graph DegreeTwoThreeSpectrum5645.graph
    sourceMap2544 fusedMap2544 sourceMap2544_checked fusedMap2544_checked
    DegreeTwoThreeFiniteComparisons.comparison2544
#print axioms sourceMap2544_checked
#print axioms fusedMap2544_checked
#print axioms certified2544
def sourceMap2544swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2544swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2544swap_checked : acceptsGraphIso
    (source (graph core2544) (root 10) 4 0) DegreeTwoThreeSpectrum5643.graph sourceMap2544swap=true := by decide +kernel
theorem fusedMap2544swap_checked : acceptsGraphIso
    (fused (graph core2544) (root 10) 4 0) DegreeTwoThreeSpectrum5645.graph fusedMap2544swap=true := by decide +kernel
theorem certified2544swap : Certified (graph core2544) (root 10) 4 0 :=
  of_native_maps core2544 DegreeTwoThreeSpectrum5643.graph DegreeTwoThreeSpectrum5645.graph
    sourceMap2544swap fusedMap2544swap sourceMap2544swap_checked fusedMap2544swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2544
#print axioms sourceMap2544swap_checked
#print axioms fusedMap2544swap_checked
#print axioms certified2544swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
