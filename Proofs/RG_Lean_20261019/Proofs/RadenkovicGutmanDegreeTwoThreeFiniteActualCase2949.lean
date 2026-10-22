/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2949 : Family 10 := level10.get ⟨1433,by decide⟩
def sourceMap2949 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2949 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2949_checked : acceptsGraphIso
    (source (graph core2949) (root 10) 0 4) DegreeTwoThreeSpectrum6891.graph sourceMap2949=true := by decide +kernel
theorem fusedMap2949_checked : acceptsGraphIso
    (fused (graph core2949) (root 10) 0 4) DegreeTwoThreeSpectrum6892.graph fusedMap2949=true := by decide +kernel
theorem certified2949 : Certified (graph core2949) (root 10) 0 4 :=
  of_native_maps core2949 DegreeTwoThreeSpectrum6891.graph DegreeTwoThreeSpectrum6892.graph
    sourceMap2949 fusedMap2949 sourceMap2949_checked fusedMap2949_checked
    DegreeTwoThreeFiniteComparisons.comparison2949
#print axioms sourceMap2949_checked
#print axioms fusedMap2949_checked
#print axioms certified2949
def sourceMap2949swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2949swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2949swap_checked : acceptsGraphIso
    (source (graph core2949) (root 10) 4 0) DegreeTwoThreeSpectrum6891.graph sourceMap2949swap=true := by decide +kernel
theorem fusedMap2949swap_checked : acceptsGraphIso
    (fused (graph core2949) (root 10) 4 0) DegreeTwoThreeSpectrum6892.graph fusedMap2949swap=true := by decide +kernel
theorem certified2949swap : Certified (graph core2949) (root 10) 4 0 :=
  of_native_maps core2949 DegreeTwoThreeSpectrum6891.graph DegreeTwoThreeSpectrum6892.graph
    sourceMap2949swap fusedMap2949swap sourceMap2949swap_checked fusedMap2949swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2949
#print axioms sourceMap2949swap_checked
#print axioms fusedMap2949swap_checked
#print axioms certified2949swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
