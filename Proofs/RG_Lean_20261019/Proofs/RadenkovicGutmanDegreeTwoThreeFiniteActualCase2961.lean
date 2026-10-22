/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2961 : Family 10 := level10.get ⟨1460,by decide⟩
def sourceMap2961 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2961 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2961_checked : acceptsGraphIso
    (source (graph core2961) (root 10) 0 4) DegreeTwoThreeSpectrum6933.graph sourceMap2961=true := by decide +kernel
theorem fusedMap2961_checked : acceptsGraphIso
    (fused (graph core2961) (root 10) 0 4) DegreeTwoThreeSpectrum6934.graph fusedMap2961=true := by decide +kernel
theorem certified2961 : Certified (graph core2961) (root 10) 0 4 :=
  of_native_maps core2961 DegreeTwoThreeSpectrum6933.graph DegreeTwoThreeSpectrum6934.graph
    sourceMap2961 fusedMap2961 sourceMap2961_checked fusedMap2961_checked
    DegreeTwoThreeFiniteComparisons.comparison2961
#print axioms sourceMap2961_checked
#print axioms fusedMap2961_checked
#print axioms certified2961
def sourceMap2961swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2961swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2961swap_checked : acceptsGraphIso
    (source (graph core2961) (root 10) 4 0) DegreeTwoThreeSpectrum6933.graph sourceMap2961swap=true := by decide +kernel
theorem fusedMap2961swap_checked : acceptsGraphIso
    (fused (graph core2961) (root 10) 4 0) DegreeTwoThreeSpectrum6934.graph fusedMap2961swap=true := by decide +kernel
theorem certified2961swap : Certified (graph core2961) (root 10) 4 0 :=
  of_native_maps core2961 DegreeTwoThreeSpectrum6933.graph DegreeTwoThreeSpectrum6934.graph
    sourceMap2961swap fusedMap2961swap sourceMap2961swap_checked fusedMap2961swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2961
#print axioms sourceMap2961swap_checked
#print axioms fusedMap2961swap_checked
#print axioms certified2961swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
