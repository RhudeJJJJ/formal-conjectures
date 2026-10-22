/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2463 : Family 10 := level10.get ⟨59,by decide⟩
def sourceMap2463 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2463 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2463_checked : acceptsGraphIso
    (source (graph core2463) (root 10) 0 4) DegreeTwoThreeSpectrum5221.graph sourceMap2463=true := by decide +kernel
theorem fusedMap2463_checked : acceptsGraphIso
    (fused (graph core2463) (root 10) 0 4) DegreeTwoThreeSpectrum4971.graph fusedMap2463=true := by decide +kernel
theorem certified2463 : Certified (graph core2463) (root 10) 0 4 :=
  of_native_maps core2463 DegreeTwoThreeSpectrum5221.graph DegreeTwoThreeSpectrum4971.graph
    sourceMap2463 fusedMap2463 sourceMap2463_checked fusedMap2463_checked
    DegreeTwoThreeFiniteComparisons.comparison2463
#print axioms sourceMap2463_checked
#print axioms fusedMap2463_checked
#print axioms certified2463
def sourceMap2463swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2463swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2463swap_checked : acceptsGraphIso
    (source (graph core2463) (root 10) 4 0) DegreeTwoThreeSpectrum5221.graph sourceMap2463swap=true := by decide +kernel
theorem fusedMap2463swap_checked : acceptsGraphIso
    (fused (graph core2463) (root 10) 4 0) DegreeTwoThreeSpectrum4971.graph fusedMap2463swap=true := by decide +kernel
theorem certified2463swap : Certified (graph core2463) (root 10) 4 0 :=
  of_native_maps core2463 DegreeTwoThreeSpectrum5221.graph DegreeTwoThreeSpectrum4971.graph
    sourceMap2463swap fusedMap2463swap sourceMap2463swap_checked fusedMap2463swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2463
#print axioms sourceMap2463swap_checked
#print axioms fusedMap2463swap_checked
#print axioms certified2463swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
