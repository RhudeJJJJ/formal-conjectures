/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2763 : Family 10 := level10.get ⟨976,by decide⟩
def sourceMap2763 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,16,6,7,8,9,10] (sourceLabel 10 0 4 v)
def fusedMap2763 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2763_checked : acceptsGraphIso
    (source (graph core2763) (root 10) 0 4) DegreeTwoThreeSpectrum7042.graph sourceMap2763=true := by decide +kernel
theorem fusedMap2763_checked : acceptsGraphIso
    (fused (graph core2763) (root 10) 0 4) DegreeTwoThreeSpectrum5910.graph fusedMap2763=true := by decide +kernel
theorem certified2763 : Certified (graph core2763) (root 10) 0 4 :=
  of_native_maps core2763 DegreeTwoThreeSpectrum7042.graph DegreeTwoThreeSpectrum5910.graph
    sourceMap2763 fusedMap2763 sourceMap2763_checked fusedMap2763_checked
    DegreeTwoThreeFiniteComparisons.comparison2763
#print axioms sourceMap2763_checked
#print axioms fusedMap2763_checked
#print axioms certified2763
def sourceMap2763swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10,16] (sourceLabel 10 4 0 v)
def fusedMap2763swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2763swap_checked : acceptsGraphIso
    (source (graph core2763) (root 10) 4 0) DegreeTwoThreeSpectrum7042.graph sourceMap2763swap=true := by decide +kernel
theorem fusedMap2763swap_checked : acceptsGraphIso
    (fused (graph core2763) (root 10) 4 0) DegreeTwoThreeSpectrum5910.graph fusedMap2763swap=true := by decide +kernel
theorem certified2763swap : Certified (graph core2763) (root 10) 4 0 :=
  of_native_maps core2763 DegreeTwoThreeSpectrum7042.graph DegreeTwoThreeSpectrum5910.graph
    sourceMap2763swap fusedMap2763swap sourceMap2763swap_checked fusedMap2763swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2763
#print axioms sourceMap2763swap_checked
#print axioms fusedMap2763swap_checked
#print axioms certified2763swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
