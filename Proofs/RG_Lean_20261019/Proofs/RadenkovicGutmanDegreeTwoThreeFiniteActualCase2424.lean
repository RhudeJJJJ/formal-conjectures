/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2424 : Family 9 := level9.get ⟨601,by decide⟩
def sourceMap2424 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2424 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2424_checked : acceptsGraphIso
    (source (graph core2424) (root 9) 0 4) DegreeTwoThreeSpectrum4735.graph sourceMap2424=true := by decide +kernel
theorem fusedMap2424_checked : acceptsGraphIso
    (fused (graph core2424) (root 9) 0 4) DegreeTwoThreeSpectrum4286.graph fusedMap2424=true := by decide +kernel
theorem certified2424 : Certified (graph core2424) (root 9) 0 4 :=
  of_native_maps core2424 DegreeTwoThreeSpectrum4735.graph DegreeTwoThreeSpectrum4286.graph
    sourceMap2424 fusedMap2424 sourceMap2424_checked fusedMap2424_checked
    DegreeTwoThreeFiniteComparisons.comparison2424
#print axioms sourceMap2424_checked
#print axioms fusedMap2424_checked
#print axioms certified2424
def sourceMap2424swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2424swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2424swap_checked : acceptsGraphIso
    (source (graph core2424) (root 9) 4 0) DegreeTwoThreeSpectrum4735.graph sourceMap2424swap=true := by decide +kernel
theorem fusedMap2424swap_checked : acceptsGraphIso
    (fused (graph core2424) (root 9) 4 0) DegreeTwoThreeSpectrum4286.graph fusedMap2424swap=true := by decide +kernel
theorem certified2424swap : Certified (graph core2424) (root 9) 4 0 :=
  of_native_maps core2424 DegreeTwoThreeSpectrum4735.graph DegreeTwoThreeSpectrum4286.graph
    sourceMap2424swap fusedMap2424swap sourceMap2424swap_checked fusedMap2424swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2424
#print axioms sourceMap2424swap_checked
#print axioms fusedMap2424swap_checked
#print axioms certified2424swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
