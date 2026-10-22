/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2249 : Family 9 := level9.get ⟨141,by decide⟩
def sourceMap2249 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2249 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2249_checked : acceptsGraphIso
    (source (graph core2249) (root 9) 0 4) DegreeTwoThreeSpectrum4203.graph sourceMap2249=true := by decide +kernel
theorem fusedMap2249_checked : acceptsGraphIso
    (fused (graph core2249) (root 9) 0 4) DegreeTwoThreeSpectrum3896.graph fusedMap2249=true := by decide +kernel
theorem certified2249 : Certified (graph core2249) (root 9) 0 4 :=
  of_native_maps core2249 DegreeTwoThreeSpectrum4203.graph DegreeTwoThreeSpectrum3896.graph
    sourceMap2249 fusedMap2249 sourceMap2249_checked fusedMap2249_checked
    DegreeTwoThreeFiniteComparisons.comparison2249
#print axioms sourceMap2249_checked
#print axioms fusedMap2249_checked
#print axioms certified2249
def sourceMap2249swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2249swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2249swap_checked : acceptsGraphIso
    (source (graph core2249) (root 9) 4 0) DegreeTwoThreeSpectrum4203.graph sourceMap2249swap=true := by decide +kernel
theorem fusedMap2249swap_checked : acceptsGraphIso
    (fused (graph core2249) (root 9) 4 0) DegreeTwoThreeSpectrum3896.graph fusedMap2249swap=true := by decide +kernel
theorem certified2249swap : Certified (graph core2249) (root 9) 4 0 :=
  of_native_maps core2249 DegreeTwoThreeSpectrum4203.graph DegreeTwoThreeSpectrum3896.graph
    sourceMap2249swap fusedMap2249swap sourceMap2249swap_checked fusedMap2249swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2249
#print axioms sourceMap2249swap_checked
#print axioms fusedMap2249swap_checked
#print axioms certified2249swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
