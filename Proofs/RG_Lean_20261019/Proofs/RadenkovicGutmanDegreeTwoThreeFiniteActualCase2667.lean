/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2667 : Family 10 := level10.get ⟨728,by decide⟩
def sourceMap2667 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2667 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2667_checked : acceptsGraphIso
    (source (graph core2667) (root 10) 0 4) DegreeTwoThreeSpectrum6596.graph sourceMap2667=true := by decide +kernel
theorem fusedMap2667_checked : acceptsGraphIso
    (fused (graph core2667) (root 10) 0 4) DegreeTwoThreeSpectrum5484.graph fusedMap2667=true := by decide +kernel
theorem certified2667 : Certified (graph core2667) (root 10) 0 4 :=
  of_native_maps core2667 DegreeTwoThreeSpectrum6596.graph DegreeTwoThreeSpectrum5484.graph
    sourceMap2667 fusedMap2667 sourceMap2667_checked fusedMap2667_checked
    DegreeTwoThreeFiniteComparisons.comparison2667
#print axioms sourceMap2667_checked
#print axioms fusedMap2667_checked
#print axioms certified2667
def sourceMap2667swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2667swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2667swap_checked : acceptsGraphIso
    (source (graph core2667) (root 10) 4 0) DegreeTwoThreeSpectrum6596.graph sourceMap2667swap=true := by decide +kernel
theorem fusedMap2667swap_checked : acceptsGraphIso
    (fused (graph core2667) (root 10) 4 0) DegreeTwoThreeSpectrum5484.graph fusedMap2667swap=true := by decide +kernel
theorem certified2667swap : Certified (graph core2667) (root 10) 4 0 :=
  of_native_maps core2667 DegreeTwoThreeSpectrum6596.graph DegreeTwoThreeSpectrum5484.graph
    sourceMap2667swap fusedMap2667swap sourceMap2667swap_checked fusedMap2667swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2667
#print axioms sourceMap2667swap_checked
#print axioms fusedMap2667swap_checked
#print axioms certified2667swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
