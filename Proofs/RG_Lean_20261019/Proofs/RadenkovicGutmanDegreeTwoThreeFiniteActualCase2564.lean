/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2564 : Family 10 := level10.get ⟨424,by decide⟩
def sourceMap2564 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2564 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2564_checked : acceptsGraphIso
    (source (graph core2564) (root 10) 0 4) DegreeTwoThreeSpectrum5811.graph sourceMap2564=true := by decide +kernel
theorem fusedMap2564_checked : acceptsGraphIso
    (fused (graph core2564) (root 10) 0 4) DegreeTwoThreeSpectrum5815.graph fusedMap2564=true := by decide +kernel
theorem certified2564 : Certified (graph core2564) (root 10) 0 4 :=
  of_native_maps core2564 DegreeTwoThreeSpectrum5811.graph DegreeTwoThreeSpectrum5815.graph
    sourceMap2564 fusedMap2564 sourceMap2564_checked fusedMap2564_checked
    DegreeTwoThreeFiniteComparisons.comparison2564
#print axioms sourceMap2564_checked
#print axioms fusedMap2564_checked
#print axioms certified2564
def sourceMap2564swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2564swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2564swap_checked : acceptsGraphIso
    (source (graph core2564) (root 10) 4 0) DegreeTwoThreeSpectrum5811.graph sourceMap2564swap=true := by decide +kernel
theorem fusedMap2564swap_checked : acceptsGraphIso
    (fused (graph core2564) (root 10) 4 0) DegreeTwoThreeSpectrum5815.graph fusedMap2564swap=true := by decide +kernel
theorem certified2564swap : Certified (graph core2564) (root 10) 4 0 :=
  of_native_maps core2564 DegreeTwoThreeSpectrum5811.graph DegreeTwoThreeSpectrum5815.graph
    sourceMap2564swap fusedMap2564swap sourceMap2564swap_checked fusedMap2564swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2564
#print axioms sourceMap2564swap_checked
#print axioms fusedMap2564swap_checked
#print axioms certified2564swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
