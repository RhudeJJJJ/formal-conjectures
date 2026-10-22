/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2669 : Family 10 := level10.get ⟨735,by decide⟩
def sourceMap2669 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2669 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2669_checked : acceptsGraphIso
    (source (graph core2669) (root 10) 0 4) DegreeTwoThreeSpectrum6617.graph sourceMap2669=true := by decide +kernel
theorem fusedMap2669_checked : acceptsGraphIso
    (fused (graph core2669) (root 10) 0 4) DegreeTwoThreeSpectrum5492.graph fusedMap2669=true := by decide +kernel
theorem certified2669 : Certified (graph core2669) (root 10) 0 4 :=
  of_native_maps core2669 DegreeTwoThreeSpectrum6617.graph DegreeTwoThreeSpectrum5492.graph
    sourceMap2669 fusedMap2669 sourceMap2669_checked fusedMap2669_checked
    DegreeTwoThreeFiniteComparisons.comparison2669
#print axioms sourceMap2669_checked
#print axioms fusedMap2669_checked
#print axioms certified2669
def sourceMap2669swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2669swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2669swap_checked : acceptsGraphIso
    (source (graph core2669) (root 10) 4 0) DegreeTwoThreeSpectrum6617.graph sourceMap2669swap=true := by decide +kernel
theorem fusedMap2669swap_checked : acceptsGraphIso
    (fused (graph core2669) (root 10) 4 0) DegreeTwoThreeSpectrum5492.graph fusedMap2669swap=true := by decide +kernel
theorem certified2669swap : Certified (graph core2669) (root 10) 4 0 :=
  of_native_maps core2669 DegreeTwoThreeSpectrum6617.graph DegreeTwoThreeSpectrum5492.graph
    sourceMap2669swap fusedMap2669swap sourceMap2669swap_checked fusedMap2669swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2669
#print axioms sourceMap2669swap_checked
#print axioms fusedMap2669swap_checked
#print axioms certified2669swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
