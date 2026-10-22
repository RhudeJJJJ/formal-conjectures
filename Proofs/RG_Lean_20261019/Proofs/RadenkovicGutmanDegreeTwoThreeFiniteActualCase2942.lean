/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2942 : Family 10 := level10.get ⟨1419,by decide⟩
def sourceMap2942 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2942 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2942_checked : acceptsGraphIso
    (source (graph core2942) (root 10) 0 4) DegreeTwoThreeSpectrum6870.graph sourceMap2942=true := by decide +kernel
theorem fusedMap2942_checked : acceptsGraphIso
    (fused (graph core2942) (root 10) 0 4) DegreeTwoThreeSpectrum6871.graph fusedMap2942=true := by decide +kernel
theorem certified2942 : Certified (graph core2942) (root 10) 0 4 :=
  of_native_maps core2942 DegreeTwoThreeSpectrum6870.graph DegreeTwoThreeSpectrum6871.graph
    sourceMap2942 fusedMap2942 sourceMap2942_checked fusedMap2942_checked
    DegreeTwoThreeFiniteComparisons.comparison2942
#print axioms sourceMap2942_checked
#print axioms fusedMap2942_checked
#print axioms certified2942
def sourceMap2942swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2942swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2942swap_checked : acceptsGraphIso
    (source (graph core2942) (root 10) 4 0) DegreeTwoThreeSpectrum6870.graph sourceMap2942swap=true := by decide +kernel
theorem fusedMap2942swap_checked : acceptsGraphIso
    (fused (graph core2942) (root 10) 4 0) DegreeTwoThreeSpectrum6871.graph fusedMap2942swap=true := by decide +kernel
theorem certified2942swap : Certified (graph core2942) (root 10) 4 0 :=
  of_native_maps core2942 DegreeTwoThreeSpectrum6870.graph DegreeTwoThreeSpectrum6871.graph
    sourceMap2942swap fusedMap2942swap sourceMap2942swap_checked fusedMap2942swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2942
#print axioms sourceMap2942swap_checked
#print axioms fusedMap2942swap_checked
#print axioms certified2942swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
