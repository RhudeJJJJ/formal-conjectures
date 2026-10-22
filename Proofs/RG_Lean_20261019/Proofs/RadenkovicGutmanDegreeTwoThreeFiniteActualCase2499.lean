/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2499 : Family 10 := level10.get ⟨205,by decide⟩
def sourceMap2499 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2499 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2499_checked : acceptsGraphIso
    (source (graph core2499) (root 10) 0 4) DegreeTwoThreeSpectrum5199.graph sourceMap2499=true := by decide +kernel
theorem fusedMap2499_checked : acceptsGraphIso
    (fused (graph core2499) (root 10) 0 4) DegreeTwoThreeSpectrum5200.graph fusedMap2499=true := by decide +kernel
theorem certified2499 : Certified (graph core2499) (root 10) 0 4 :=
  of_native_maps core2499 DegreeTwoThreeSpectrum5199.graph DegreeTwoThreeSpectrum5200.graph
    sourceMap2499 fusedMap2499 sourceMap2499_checked fusedMap2499_checked
    DegreeTwoThreeFiniteComparisons.comparison2499
#print axioms sourceMap2499_checked
#print axioms fusedMap2499_checked
#print axioms certified2499
def sourceMap2499swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2499swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2499swap_checked : acceptsGraphIso
    (source (graph core2499) (root 10) 4 0) DegreeTwoThreeSpectrum5199.graph sourceMap2499swap=true := by decide +kernel
theorem fusedMap2499swap_checked : acceptsGraphIso
    (fused (graph core2499) (root 10) 4 0) DegreeTwoThreeSpectrum5200.graph fusedMap2499swap=true := by decide +kernel
theorem certified2499swap : Certified (graph core2499) (root 10) 4 0 :=
  of_native_maps core2499 DegreeTwoThreeSpectrum5199.graph DegreeTwoThreeSpectrum5200.graph
    sourceMap2499swap fusedMap2499swap sourceMap2499swap_checked fusedMap2499swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2499
#print axioms sourceMap2499swap_checked
#print axioms fusedMap2499swap_checked
#print axioms certified2499swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
