/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2310 : Family 9 := level9.get ⟨320,by decide⟩
def sourceMap2310 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2310 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2310_checked : acceptsGraphIso
    (source (graph core2310) (root 9) 0 4) DegreeTwoThreeSpectrum4180.graph sourceMap2310=true := by decide +kernel
theorem fusedMap2310_checked : acceptsGraphIso
    (fused (graph core2310) (root 9) 0 4) DegreeTwoThreeSpectrum4181.graph fusedMap2310=true := by decide +kernel
theorem certified2310 : Certified (graph core2310) (root 9) 0 4 :=
  of_native_maps core2310 DegreeTwoThreeSpectrum4180.graph DegreeTwoThreeSpectrum4181.graph
    sourceMap2310 fusedMap2310 sourceMap2310_checked fusedMap2310_checked
    DegreeTwoThreeFiniteComparisons.comparison2310
#print axioms sourceMap2310_checked
#print axioms fusedMap2310_checked
#print axioms certified2310
def sourceMap2310swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2310swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2310swap_checked : acceptsGraphIso
    (source (graph core2310) (root 9) 4 0) DegreeTwoThreeSpectrum4180.graph sourceMap2310swap=true := by decide +kernel
theorem fusedMap2310swap_checked : acceptsGraphIso
    (fused (graph core2310) (root 9) 4 0) DegreeTwoThreeSpectrum4181.graph fusedMap2310swap=true := by decide +kernel
theorem certified2310swap : Certified (graph core2310) (root 9) 4 0 :=
  of_native_maps core2310 DegreeTwoThreeSpectrum4180.graph DegreeTwoThreeSpectrum4181.graph
    sourceMap2310swap fusedMap2310swap sourceMap2310swap_checked fusedMap2310swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2310
#print axioms sourceMap2310swap_checked
#print axioms fusedMap2310swap_checked
#print axioms certified2310swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
