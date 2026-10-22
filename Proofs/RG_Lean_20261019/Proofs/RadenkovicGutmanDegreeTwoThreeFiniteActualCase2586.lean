/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2586 : Family 10 := level10.get ⟨485,by decide⟩
def sourceMap2586 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,6,7,8,9,1,2,3,4,5] (sourceLabel 10 0 4 v)
def fusedMap2586 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2586_checked : acceptsGraphIso
    (source (graph core2586) (root 10) 0 4) DegreeTwoThreeSpectrum5932.graph sourceMap2586=true := by decide +kernel
theorem fusedMap2586_checked : acceptsGraphIso
    (fused (graph core2586) (root 10) 0 4) DegreeTwoThreeSpectrum5951.graph fusedMap2586=true := by decide +kernel
theorem certified2586 : Certified (graph core2586) (root 10) 0 4 :=
  of_native_maps core2586 DegreeTwoThreeSpectrum5932.graph DegreeTwoThreeSpectrum5951.graph
    sourceMap2586 fusedMap2586 sourceMap2586_checked fusedMap2586_checked
    DegreeTwoThreeFiniteComparisons.comparison2586
#print axioms sourceMap2586_checked
#print axioms fusedMap2586_checked
#print axioms certified2586
def sourceMap2586swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,6,7,8,1,2,3,4,5,9] (sourceLabel 10 4 0 v)
def fusedMap2586swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2586swap_checked : acceptsGraphIso
    (source (graph core2586) (root 10) 4 0) DegreeTwoThreeSpectrum5932.graph sourceMap2586swap=true := by decide +kernel
theorem fusedMap2586swap_checked : acceptsGraphIso
    (fused (graph core2586) (root 10) 4 0) DegreeTwoThreeSpectrum5951.graph fusedMap2586swap=true := by decide +kernel
theorem certified2586swap : Certified (graph core2586) (root 10) 4 0 :=
  of_native_maps core2586 DegreeTwoThreeSpectrum5932.graph DegreeTwoThreeSpectrum5951.graph
    sourceMap2586swap fusedMap2586swap sourceMap2586swap_checked fusedMap2586swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2586
#print axioms sourceMap2586swap_checked
#print axioms fusedMap2586swap_checked
#print axioms certified2586swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
