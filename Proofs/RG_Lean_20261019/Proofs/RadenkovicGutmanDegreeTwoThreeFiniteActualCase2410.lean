/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2410 : Family 9 := level9.get ⟨570,by decide⟩
def sourceMap2410 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2410 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2410_checked : acceptsGraphIso
    (source (graph core2410) (root 9) 0 4) DegreeTwoThreeSpectrum4699.graph sourceMap2410=true := by decide +kernel
theorem fusedMap2410_checked : acceptsGraphIso
    (fused (graph core2410) (root 9) 0 4) DegreeTwoThreeSpectrum4216.graph fusedMap2410=true := by decide +kernel
theorem certified2410 : Certified (graph core2410) (root 9) 0 4 :=
  of_native_maps core2410 DegreeTwoThreeSpectrum4699.graph DegreeTwoThreeSpectrum4216.graph
    sourceMap2410 fusedMap2410 sourceMap2410_checked fusedMap2410_checked
    DegreeTwoThreeFiniteComparisons.comparison2410
#print axioms sourceMap2410_checked
#print axioms fusedMap2410_checked
#print axioms certified2410
def sourceMap2410swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2410swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2410swap_checked : acceptsGraphIso
    (source (graph core2410) (root 9) 4 0) DegreeTwoThreeSpectrum4699.graph sourceMap2410swap=true := by decide +kernel
theorem fusedMap2410swap_checked : acceptsGraphIso
    (fused (graph core2410) (root 9) 4 0) DegreeTwoThreeSpectrum4216.graph fusedMap2410swap=true := by decide +kernel
theorem certified2410swap : Certified (graph core2410) (root 9) 4 0 :=
  of_native_maps core2410 DegreeTwoThreeSpectrum4699.graph DegreeTwoThreeSpectrum4216.graph
    sourceMap2410swap fusedMap2410swap sourceMap2410swap_checked fusedMap2410swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2410
#print axioms sourceMap2410swap_checked
#print axioms fusedMap2410swap_checked
#print axioms certified2410swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
