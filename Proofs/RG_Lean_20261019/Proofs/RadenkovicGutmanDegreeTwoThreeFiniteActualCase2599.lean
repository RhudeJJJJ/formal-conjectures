/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2599 : Family 10 := level10.get ⟨531,by decide⟩
def sourceMap2599 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2599 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2599_checked : acceptsGraphIso
    (source (graph core2599) (root 10) 0 4) DegreeTwoThreeSpectrum6111.graph sourceMap2599=true := by decide +kernel
theorem fusedMap2599_checked : acceptsGraphIso
    (fused (graph core2599) (root 10) 0 4) DegreeTwoThreeSpectrum5176.graph fusedMap2599=true := by decide +kernel
theorem certified2599 : Certified (graph core2599) (root 10) 0 4 :=
  of_native_maps core2599 DegreeTwoThreeSpectrum6111.graph DegreeTwoThreeSpectrum5176.graph
    sourceMap2599 fusedMap2599 sourceMap2599_checked fusedMap2599_checked
    DegreeTwoThreeFiniteComparisons.comparison2599
#print axioms sourceMap2599_checked
#print axioms fusedMap2599_checked
#print axioms certified2599
def sourceMap2599swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2599swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2599swap_checked : acceptsGraphIso
    (source (graph core2599) (root 10) 4 0) DegreeTwoThreeSpectrum6111.graph sourceMap2599swap=true := by decide +kernel
theorem fusedMap2599swap_checked : acceptsGraphIso
    (fused (graph core2599) (root 10) 4 0) DegreeTwoThreeSpectrum5176.graph fusedMap2599swap=true := by decide +kernel
theorem certified2599swap : Certified (graph core2599) (root 10) 4 0 :=
  of_native_maps core2599 DegreeTwoThreeSpectrum6111.graph DegreeTwoThreeSpectrum5176.graph
    sourceMap2599swap fusedMap2599swap sourceMap2599swap_checked fusedMap2599swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2599
#print axioms sourceMap2599swap_checked
#print axioms fusedMap2599swap_checked
#print axioms certified2599swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
