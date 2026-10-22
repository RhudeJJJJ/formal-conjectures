/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2100 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap2100 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2100 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2100_checked : acceptsGraphIso
    (source (graph core2100) (root 7) 0 4) DegreeTwoThreeSpectrum1909.graph sourceMap2100=true := by decide +kernel
theorem fusedMap2100_checked : acceptsGraphIso
    (fused (graph core2100) (root 7) 0 4) DegreeTwoThreeSpectrum1911.graph fusedMap2100=true := by decide +kernel
theorem certified2100 : Certified (graph core2100) (root 7) 0 4 :=
  of_native_maps core2100 DegreeTwoThreeSpectrum1909.graph DegreeTwoThreeSpectrum1911.graph
    sourceMap2100 fusedMap2100 sourceMap2100_checked fusedMap2100_checked
    DegreeTwoThreeFiniteComparisons.comparison2100
#print axioms sourceMap2100_checked
#print axioms fusedMap2100_checked
#print axioms certified2100
def sourceMap2100swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2100swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2100swap_checked : acceptsGraphIso
    (source (graph core2100) (root 7) 4 0) DegreeTwoThreeSpectrum1909.graph sourceMap2100swap=true := by decide +kernel
theorem fusedMap2100swap_checked : acceptsGraphIso
    (fused (graph core2100) (root 7) 4 0) DegreeTwoThreeSpectrum1911.graph fusedMap2100swap=true := by decide +kernel
theorem certified2100swap : Certified (graph core2100) (root 7) 4 0 :=
  of_native_maps core2100 DegreeTwoThreeSpectrum1909.graph DegreeTwoThreeSpectrum1911.graph
    sourceMap2100swap fusedMap2100swap sourceMap2100swap_checked fusedMap2100swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2100
#print axioms sourceMap2100swap_checked
#print axioms fusedMap2100swap_checked
#print axioms certified2100swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
