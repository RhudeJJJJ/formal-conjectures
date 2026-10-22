/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2511 : Family 10 := level10.get ⟨253,by decide⟩
def sourceMap2511 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2511 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2511_checked : acceptsGraphIso
    (source (graph core2511) (root 10) 0 4) DegreeTwoThreeSpectrum5349.graph sourceMap2511=true := by decide +kernel
theorem fusedMap2511_checked : acceptsGraphIso
    (fused (graph core2511) (root 10) 0 4) DegreeTwoThreeSpectrum5350.graph fusedMap2511=true := by decide +kernel
theorem certified2511 : Certified (graph core2511) (root 10) 0 4 :=
  of_native_maps core2511 DegreeTwoThreeSpectrum5349.graph DegreeTwoThreeSpectrum5350.graph
    sourceMap2511 fusedMap2511 sourceMap2511_checked fusedMap2511_checked
    DegreeTwoThreeFiniteComparisons.comparison2511
#print axioms sourceMap2511_checked
#print axioms fusedMap2511_checked
#print axioms certified2511
def sourceMap2511swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2511swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2511swap_checked : acceptsGraphIso
    (source (graph core2511) (root 10) 4 0) DegreeTwoThreeSpectrum5349.graph sourceMap2511swap=true := by decide +kernel
theorem fusedMap2511swap_checked : acceptsGraphIso
    (fused (graph core2511) (root 10) 4 0) DegreeTwoThreeSpectrum5350.graph fusedMap2511swap=true := by decide +kernel
theorem certified2511swap : Certified (graph core2511) (root 10) 4 0 :=
  of_native_maps core2511 DegreeTwoThreeSpectrum5349.graph DegreeTwoThreeSpectrum5350.graph
    sourceMap2511swap fusedMap2511swap sourceMap2511swap_checked fusedMap2511swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2511
#print axioms sourceMap2511swap_checked
#print axioms fusedMap2511swap_checked
#print axioms certified2511swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
