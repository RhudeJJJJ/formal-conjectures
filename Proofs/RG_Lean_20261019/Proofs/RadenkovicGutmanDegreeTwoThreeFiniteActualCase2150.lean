/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2150 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap2150 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2150 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2150_checked : acceptsGraphIso
    (source (graph core2150) (root 8) 0 4) DegreeTwoThreeSpectrum2526.graph sourceMap2150=true := by decide +kernel
theorem fusedMap2150_checked : acceptsGraphIso
    (fused (graph core2150) (root 8) 0 4) DegreeTwoThreeSpectrum2528.graph fusedMap2150=true := by decide +kernel
theorem certified2150 : Certified (graph core2150) (root 8) 0 4 :=
  of_native_maps core2150 DegreeTwoThreeSpectrum2526.graph DegreeTwoThreeSpectrum2528.graph
    sourceMap2150 fusedMap2150 sourceMap2150_checked fusedMap2150_checked
    DegreeTwoThreeFiniteComparisons.comparison2150
#print axioms sourceMap2150_checked
#print axioms fusedMap2150_checked
#print axioms certified2150
def sourceMap2150swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2150swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2150swap_checked : acceptsGraphIso
    (source (graph core2150) (root 8) 4 0) DegreeTwoThreeSpectrum2526.graph sourceMap2150swap=true := by decide +kernel
theorem fusedMap2150swap_checked : acceptsGraphIso
    (fused (graph core2150) (root 8) 4 0) DegreeTwoThreeSpectrum2528.graph fusedMap2150swap=true := by decide +kernel
theorem certified2150swap : Certified (graph core2150) (root 8) 4 0 :=
  of_native_maps core2150 DegreeTwoThreeSpectrum2526.graph DegreeTwoThreeSpectrum2528.graph
    sourceMap2150swap fusedMap2150swap sourceMap2150swap_checked fusedMap2150swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2150
#print axioms sourceMap2150swap_checked
#print axioms fusedMap2150swap_checked
#print axioms certified2150swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
