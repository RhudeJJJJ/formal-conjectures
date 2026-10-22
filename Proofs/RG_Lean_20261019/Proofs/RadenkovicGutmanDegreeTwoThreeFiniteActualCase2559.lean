/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2559 : Family 10 := level10.get ⟨413,by decide⟩
def sourceMap2559 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2559 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2559_checked : acceptsGraphIso
    (source (graph core2559) (root 10) 0 4) DegreeTwoThreeSpectrum5788.graph sourceMap2559=true := by decide +kernel
theorem fusedMap2559_checked : acceptsGraphIso
    (fused (graph core2559) (root 10) 0 4) DegreeTwoThreeSpectrum5789.graph fusedMap2559=true := by decide +kernel
theorem certified2559 : Certified (graph core2559) (root 10) 0 4 :=
  of_native_maps core2559 DegreeTwoThreeSpectrum5788.graph DegreeTwoThreeSpectrum5789.graph
    sourceMap2559 fusedMap2559 sourceMap2559_checked fusedMap2559_checked
    DegreeTwoThreeFiniteComparisons.comparison2559
#print axioms sourceMap2559_checked
#print axioms fusedMap2559_checked
#print axioms certified2559
def sourceMap2559swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2559swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2559swap_checked : acceptsGraphIso
    (source (graph core2559) (root 10) 4 0) DegreeTwoThreeSpectrum5788.graph sourceMap2559swap=true := by decide +kernel
theorem fusedMap2559swap_checked : acceptsGraphIso
    (fused (graph core2559) (root 10) 4 0) DegreeTwoThreeSpectrum5789.graph fusedMap2559swap=true := by decide +kernel
theorem certified2559swap : Certified (graph core2559) (root 10) 4 0 :=
  of_native_maps core2559 DegreeTwoThreeSpectrum5788.graph DegreeTwoThreeSpectrum5789.graph
    sourceMap2559swap fusedMap2559swap sourceMap2559swap_checked fusedMap2559swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2559
#print axioms sourceMap2559swap_checked
#print axioms fusedMap2559swap_checked
#print axioms certified2559swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
