/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2794 : Family 10 := level10.get ⟨1061,by decide⟩
def sourceMap2794 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2794 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2794_checked : acceptsGraphIso
    (source (graph core2794) (root 10) 0 4) DegreeTwoThreeSpectrum6106.graph sourceMap2794=true := by decide +kernel
theorem fusedMap2794_checked : acceptsGraphIso
    (fused (graph core2794) (root 10) 0 4) DegreeTwoThreeSpectrum6107.graph fusedMap2794=true := by decide +kernel
theorem certified2794 : Certified (graph core2794) (root 10) 0 4 :=
  of_native_maps core2794 DegreeTwoThreeSpectrum6106.graph DegreeTwoThreeSpectrum6107.graph
    sourceMap2794 fusedMap2794 sourceMap2794_checked fusedMap2794_checked
    DegreeTwoThreeFiniteComparisons.comparison2794
#print axioms sourceMap2794_checked
#print axioms fusedMap2794_checked
#print axioms certified2794
def sourceMap2794swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2794swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2794swap_checked : acceptsGraphIso
    (source (graph core2794) (root 10) 4 0) DegreeTwoThreeSpectrum6106.graph sourceMap2794swap=true := by decide +kernel
theorem fusedMap2794swap_checked : acceptsGraphIso
    (fused (graph core2794) (root 10) 4 0) DegreeTwoThreeSpectrum6107.graph fusedMap2794swap=true := by decide +kernel
theorem certified2794swap : Certified (graph core2794) (root 10) 4 0 :=
  of_native_maps core2794 DegreeTwoThreeSpectrum6106.graph DegreeTwoThreeSpectrum6107.graph
    sourceMap2794swap fusedMap2794swap sourceMap2794swap_checked fusedMap2794swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2794
#print axioms sourceMap2794swap_checked
#print axioms fusedMap2794swap_checked
#print axioms certified2794swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
