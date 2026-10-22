/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2198 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap2198 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2198 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2198_checked : acceptsGraphIso
    (source (graph core2198) (root 8) 0 4) DegreeTwoThreeSpectrum3303.graph sourceMap2198=true := by decide +kernel
theorem fusedMap2198_checked : acceptsGraphIso
    (fused (graph core2198) (root 8) 0 4) DegreeTwoThreeSpectrum2566.graph fusedMap2198=true := by decide +kernel
theorem certified2198 : Certified (graph core2198) (root 8) 0 4 :=
  of_native_maps core2198 DegreeTwoThreeSpectrum3303.graph DegreeTwoThreeSpectrum2566.graph
    sourceMap2198 fusedMap2198 sourceMap2198_checked fusedMap2198_checked
    DegreeTwoThreeFiniteComparisons.comparison2198
#print axioms sourceMap2198_checked
#print axioms fusedMap2198_checked
#print axioms certified2198
def sourceMap2198swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2198swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2198swap_checked : acceptsGraphIso
    (source (graph core2198) (root 8) 4 0) DegreeTwoThreeSpectrum3303.graph sourceMap2198swap=true := by decide +kernel
theorem fusedMap2198swap_checked : acceptsGraphIso
    (fused (graph core2198) (root 8) 4 0) DegreeTwoThreeSpectrum2566.graph fusedMap2198swap=true := by decide +kernel
theorem certified2198swap : Certified (graph core2198) (root 8) 4 0 :=
  of_native_maps core2198 DegreeTwoThreeSpectrum3303.graph DegreeTwoThreeSpectrum2566.graph
    sourceMap2198swap fusedMap2198swap sourceMap2198swap_checked fusedMap2198swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2198
#print axioms sourceMap2198swap_checked
#print axioms fusedMap2198swap_checked
#print axioms certified2198swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
