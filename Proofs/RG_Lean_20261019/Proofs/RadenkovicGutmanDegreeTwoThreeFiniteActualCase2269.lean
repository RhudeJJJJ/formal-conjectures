/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2269 : Family 9 := level9.get ⟨207,by decide⟩
def sourceMap2269 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2269 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2269_checked : acceptsGraphIso
    (source (graph core2269) (root 9) 0 4) DegreeTwoThreeSpectrum4429.graph sourceMap2269=true := by decide +kernel
theorem fusedMap2269_checked : acceptsGraphIso
    (fused (graph core2269) (root 9) 0 4) DegreeTwoThreeSpectrum3990.graph fusedMap2269=true := by decide +kernel
theorem certified2269 : Certified (graph core2269) (root 9) 0 4 :=
  of_native_maps core2269 DegreeTwoThreeSpectrum4429.graph DegreeTwoThreeSpectrum3990.graph
    sourceMap2269 fusedMap2269 sourceMap2269_checked fusedMap2269_checked
    DegreeTwoThreeFiniteComparisons.comparison2269
#print axioms sourceMap2269_checked
#print axioms fusedMap2269_checked
#print axioms certified2269
def sourceMap2269swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2269swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2269swap_checked : acceptsGraphIso
    (source (graph core2269) (root 9) 4 0) DegreeTwoThreeSpectrum4429.graph sourceMap2269swap=true := by decide +kernel
theorem fusedMap2269swap_checked : acceptsGraphIso
    (fused (graph core2269) (root 9) 4 0) DegreeTwoThreeSpectrum3990.graph fusedMap2269swap=true := by decide +kernel
theorem certified2269swap : Certified (graph core2269) (root 9) 4 0 :=
  of_native_maps core2269 DegreeTwoThreeSpectrum4429.graph DegreeTwoThreeSpectrum3990.graph
    sourceMap2269swap fusedMap2269swap sourceMap2269swap_checked fusedMap2269swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2269
#print axioms sourceMap2269swap_checked
#print axioms fusedMap2269swap_checked
#print axioms certified2269swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
