/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2767 : Family 10 := level10.get ⟨981,by decide⟩
def sourceMap2767 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2767 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2767_checked : acceptsGraphIso
    (source (graph core2767) (root 10) 0 4) DegreeTwoThreeSpectrum7047.graph sourceMap2767=true := by decide +kernel
theorem fusedMap2767_checked : acceptsGraphIso
    (fused (graph core2767) (root 10) 0 4) DegreeTwoThreeSpectrum5916.graph fusedMap2767=true := by decide +kernel
theorem certified2767 : Certified (graph core2767) (root 10) 0 4 :=
  of_native_maps core2767 DegreeTwoThreeSpectrum7047.graph DegreeTwoThreeSpectrum5916.graph
    sourceMap2767 fusedMap2767 sourceMap2767_checked fusedMap2767_checked
    DegreeTwoThreeFiniteComparisons.comparison2767
#print axioms sourceMap2767_checked
#print axioms fusedMap2767_checked
#print axioms certified2767
def sourceMap2767swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2767swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2767swap_checked : acceptsGraphIso
    (source (graph core2767) (root 10) 4 0) DegreeTwoThreeSpectrum7047.graph sourceMap2767swap=true := by decide +kernel
theorem fusedMap2767swap_checked : acceptsGraphIso
    (fused (graph core2767) (root 10) 4 0) DegreeTwoThreeSpectrum5916.graph fusedMap2767swap=true := by decide +kernel
theorem certified2767swap : Certified (graph core2767) (root 10) 4 0 :=
  of_native_maps core2767 DegreeTwoThreeSpectrum7047.graph DegreeTwoThreeSpectrum5916.graph
    sourceMap2767swap fusedMap2767swap sourceMap2767swap_checked fusedMap2767swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2767
#print axioms sourceMap2767swap_checked
#print axioms fusedMap2767swap_checked
#print axioms certified2767swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
