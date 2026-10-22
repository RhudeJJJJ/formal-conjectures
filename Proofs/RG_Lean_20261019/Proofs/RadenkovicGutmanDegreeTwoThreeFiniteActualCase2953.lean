/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2953 : Family 10 := level10.get ⟨1443,by decide⟩
def sourceMap2953 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2953 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2953_checked : acceptsGraphIso
    (source (graph core2953) (root 10) 0 4) DegreeTwoThreeSpectrum6904.graph sourceMap2953=true := by decide +kernel
theorem fusedMap2953_checked : acceptsGraphIso
    (fused (graph core2953) (root 10) 0 4) DegreeTwoThreeSpectrum6905.graph fusedMap2953=true := by decide +kernel
theorem certified2953 : Certified (graph core2953) (root 10) 0 4 :=
  of_native_maps core2953 DegreeTwoThreeSpectrum6904.graph DegreeTwoThreeSpectrum6905.graph
    sourceMap2953 fusedMap2953 sourceMap2953_checked fusedMap2953_checked
    DegreeTwoThreeFiniteComparisons.comparison2953
#print axioms sourceMap2953_checked
#print axioms fusedMap2953_checked
#print axioms certified2953
def sourceMap2953swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2953swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2953swap_checked : acceptsGraphIso
    (source (graph core2953) (root 10) 4 0) DegreeTwoThreeSpectrum6904.graph sourceMap2953swap=true := by decide +kernel
theorem fusedMap2953swap_checked : acceptsGraphIso
    (fused (graph core2953) (root 10) 4 0) DegreeTwoThreeSpectrum6905.graph fusedMap2953swap=true := by decide +kernel
theorem certified2953swap : Certified (graph core2953) (root 10) 4 0 :=
  of_native_maps core2953 DegreeTwoThreeSpectrum6904.graph DegreeTwoThreeSpectrum6905.graph
    sourceMap2953swap fusedMap2953swap sourceMap2953swap_checked fusedMap2953swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2953
#print axioms sourceMap2953swap_checked
#print axioms fusedMap2953swap_checked
#print axioms certified2953swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
