/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2231 : Family 9 := level9.get ⟨83,by decide⟩
def sourceMap2231 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2231 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2231_checked : acceptsGraphIso
    (source (graph core2231) (root 9) 0 4) DegreeTwoThreeSpectrum4034.graph sourceMap2231=true := by decide +kernel
theorem fusedMap2231_checked : acceptsGraphIso
    (fused (graph core2231) (root 9) 0 4) DegreeTwoThreeSpectrum4035.graph fusedMap2231=true := by decide +kernel
theorem certified2231 : Certified (graph core2231) (root 9) 0 4 :=
  of_native_maps core2231 DegreeTwoThreeSpectrum4034.graph DegreeTwoThreeSpectrum4035.graph
    sourceMap2231 fusedMap2231 sourceMap2231_checked fusedMap2231_checked
    DegreeTwoThreeFiniteComparisons.comparison2231
#print axioms sourceMap2231_checked
#print axioms fusedMap2231_checked
#print axioms certified2231
def sourceMap2231swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2231swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2231swap_checked : acceptsGraphIso
    (source (graph core2231) (root 9) 4 0) DegreeTwoThreeSpectrum4034.graph sourceMap2231swap=true := by decide +kernel
theorem fusedMap2231swap_checked : acceptsGraphIso
    (fused (graph core2231) (root 9) 4 0) DegreeTwoThreeSpectrum4035.graph fusedMap2231swap=true := by decide +kernel
theorem certified2231swap : Certified (graph core2231) (root 9) 4 0 :=
  of_native_maps core2231 DegreeTwoThreeSpectrum4034.graph DegreeTwoThreeSpectrum4035.graph
    sourceMap2231swap fusedMap2231swap sourceMap2231swap_checked fusedMap2231swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2231
#print axioms sourceMap2231swap_checked
#print axioms fusedMap2231swap_checked
#print axioms certified2231swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
