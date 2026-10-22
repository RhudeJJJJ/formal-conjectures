/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2920 : Family 10 := level10.get ⟨1366,by decide⟩
def sourceMap2920 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2920 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2920_checked : acceptsGraphIso
    (source (graph core2920) (root 10) 0 4) DegreeTwoThreeSpectrum6705.graph sourceMap2920=true := by decide +kernel
theorem fusedMap2920_checked : acceptsGraphIso
    (fused (graph core2920) (root 10) 0 4) DegreeTwoThreeSpectrum6706.graph fusedMap2920=true := by decide +kernel
theorem certified2920 : Certified (graph core2920) (root 10) 0 4 :=
  of_native_maps core2920 DegreeTwoThreeSpectrum6705.graph DegreeTwoThreeSpectrum6706.graph
    sourceMap2920 fusedMap2920 sourceMap2920_checked fusedMap2920_checked
    DegreeTwoThreeFiniteComparisons.comparison2920
#print axioms sourceMap2920_checked
#print axioms fusedMap2920_checked
#print axioms certified2920
def sourceMap2920swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2920swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2920swap_checked : acceptsGraphIso
    (source (graph core2920) (root 10) 4 0) DegreeTwoThreeSpectrum6705.graph sourceMap2920swap=true := by decide +kernel
theorem fusedMap2920swap_checked : acceptsGraphIso
    (fused (graph core2920) (root 10) 4 0) DegreeTwoThreeSpectrum6706.graph fusedMap2920swap=true := by decide +kernel
theorem certified2920swap : Certified (graph core2920) (root 10) 4 0 :=
  of_native_maps core2920 DegreeTwoThreeSpectrum6705.graph DegreeTwoThreeSpectrum6706.graph
    sourceMap2920swap fusedMap2920swap sourceMap2920swap_checked fusedMap2920swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2920
#print axioms sourceMap2920swap_checked
#print axioms fusedMap2920swap_checked
#print axioms certified2920swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
