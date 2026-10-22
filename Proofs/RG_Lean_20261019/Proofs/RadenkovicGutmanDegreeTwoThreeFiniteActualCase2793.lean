/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2793 : Family 10 := level10.get ⟨1059,by decide⟩
def sourceMap2793 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2793 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2793_checked : acceptsGraphIso
    (source (graph core2793) (root 10) 0 4) DegreeTwoThreeSpectrum6102.graph sourceMap2793=true := by decide +kernel
theorem fusedMap2793_checked : acceptsGraphIso
    (fused (graph core2793) (root 10) 0 4) DegreeTwoThreeSpectrum6103.graph fusedMap2793=true := by decide +kernel
theorem certified2793 : Certified (graph core2793) (root 10) 0 4 :=
  of_native_maps core2793 DegreeTwoThreeSpectrum6102.graph DegreeTwoThreeSpectrum6103.graph
    sourceMap2793 fusedMap2793 sourceMap2793_checked fusedMap2793_checked
    DegreeTwoThreeFiniteComparisons.comparison2793
#print axioms sourceMap2793_checked
#print axioms fusedMap2793_checked
#print axioms certified2793
def sourceMap2793swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2793swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2793swap_checked : acceptsGraphIso
    (source (graph core2793) (root 10) 4 0) DegreeTwoThreeSpectrum6102.graph sourceMap2793swap=true := by decide +kernel
theorem fusedMap2793swap_checked : acceptsGraphIso
    (fused (graph core2793) (root 10) 4 0) DegreeTwoThreeSpectrum6103.graph fusedMap2793swap=true := by decide +kernel
theorem certified2793swap : Certified (graph core2793) (root 10) 4 0 :=
  of_native_maps core2793 DegreeTwoThreeSpectrum6102.graph DegreeTwoThreeSpectrum6103.graph
    sourceMap2793swap fusedMap2793swap sourceMap2793swap_checked fusedMap2793swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2793
#print axioms sourceMap2793swap_checked
#print axioms fusedMap2793swap_checked
#print axioms certified2793swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
