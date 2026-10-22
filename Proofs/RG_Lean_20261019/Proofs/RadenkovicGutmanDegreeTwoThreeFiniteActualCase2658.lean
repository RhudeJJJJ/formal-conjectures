/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2658 : Family 10 := level10.get ⟨704,by decide⟩
def sourceMap2658 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2658 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2658_checked : acceptsGraphIso
    (source (graph core2658) (root 10) 0 4) DegreeTwoThreeSpectrum6545.graph sourceMap2658=true := by decide +kernel
theorem fusedMap2658_checked : acceptsGraphIso
    (fused (graph core2658) (root 10) 0 4) DegreeTwoThreeSpectrum5445.graph fusedMap2658=true := by decide +kernel
theorem certified2658 : Certified (graph core2658) (root 10) 0 4 :=
  of_native_maps core2658 DegreeTwoThreeSpectrum6545.graph DegreeTwoThreeSpectrum5445.graph
    sourceMap2658 fusedMap2658 sourceMap2658_checked fusedMap2658_checked
    DegreeTwoThreeFiniteComparisons.comparison2658
#print axioms sourceMap2658_checked
#print axioms fusedMap2658_checked
#print axioms certified2658
def sourceMap2658swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2658swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2658swap_checked : acceptsGraphIso
    (source (graph core2658) (root 10) 4 0) DegreeTwoThreeSpectrum6545.graph sourceMap2658swap=true := by decide +kernel
theorem fusedMap2658swap_checked : acceptsGraphIso
    (fused (graph core2658) (root 10) 4 0) DegreeTwoThreeSpectrum5445.graph fusedMap2658swap=true := by decide +kernel
theorem certified2658swap : Certified (graph core2658) (root 10) 4 0 :=
  of_native_maps core2658 DegreeTwoThreeSpectrum6545.graph DegreeTwoThreeSpectrum5445.graph
    sourceMap2658swap fusedMap2658swap sourceMap2658swap_checked fusedMap2658swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2658
#print axioms sourceMap2658swap_checked
#print axioms fusedMap2658swap_checked
#print axioms certified2658swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
