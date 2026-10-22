/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2614 : Family 10 := level10.get ⟨575,by decide⟩
def sourceMap2614 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2614 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2614_checked : acceptsGraphIso
    (source (graph core2614) (root 10) 0 4) DegreeTwoThreeSpectrum6236.graph sourceMap2614=true := by decide +kernel
theorem fusedMap2614_checked : acceptsGraphIso
    (fused (graph core2614) (root 10) 0 4) DegreeTwoThreeSpectrum5242.graph fusedMap2614=true := by decide +kernel
theorem certified2614 : Certified (graph core2614) (root 10) 0 4 :=
  of_native_maps core2614 DegreeTwoThreeSpectrum6236.graph DegreeTwoThreeSpectrum5242.graph
    sourceMap2614 fusedMap2614 sourceMap2614_checked fusedMap2614_checked
    DegreeTwoThreeFiniteComparisons.comparison2614
#print axioms sourceMap2614_checked
#print axioms fusedMap2614_checked
#print axioms certified2614
def sourceMap2614swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2614swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2614swap_checked : acceptsGraphIso
    (source (graph core2614) (root 10) 4 0) DegreeTwoThreeSpectrum6236.graph sourceMap2614swap=true := by decide +kernel
theorem fusedMap2614swap_checked : acceptsGraphIso
    (fused (graph core2614) (root 10) 4 0) DegreeTwoThreeSpectrum5242.graph fusedMap2614swap=true := by decide +kernel
theorem certified2614swap : Certified (graph core2614) (root 10) 4 0 :=
  of_native_maps core2614 DegreeTwoThreeSpectrum6236.graph DegreeTwoThreeSpectrum5242.graph
    sourceMap2614swap fusedMap2614swap sourceMap2614swap_checked fusedMap2614swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2614
#print axioms sourceMap2614swap_checked
#print axioms fusedMap2614swap_checked
#print axioms certified2614swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
