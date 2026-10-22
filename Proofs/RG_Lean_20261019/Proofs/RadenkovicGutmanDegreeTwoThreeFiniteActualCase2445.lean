/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2445 : Family 9 := level9.get ⟨654,by decide⟩
def sourceMap2445 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2445 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2445_checked : acceptsGraphIso
    (source (graph core2445) (root 9) 0 4) DegreeTwoThreeSpectrum4818.graph sourceMap2445=true := by decide +kernel
theorem fusedMap2445_checked : acceptsGraphIso
    (fused (graph core2445) (root 9) 0 4) DegreeTwoThreeSpectrum4446.graph fusedMap2445=true := by decide +kernel
theorem certified2445 : Certified (graph core2445) (root 9) 0 4 :=
  of_native_maps core2445 DegreeTwoThreeSpectrum4818.graph DegreeTwoThreeSpectrum4446.graph
    sourceMap2445 fusedMap2445 sourceMap2445_checked fusedMap2445_checked
    DegreeTwoThreeFiniteComparisons.comparison2445
#print axioms sourceMap2445_checked
#print axioms fusedMap2445_checked
#print axioms certified2445
def sourceMap2445swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2445swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2445swap_checked : acceptsGraphIso
    (source (graph core2445) (root 9) 4 0) DegreeTwoThreeSpectrum4818.graph sourceMap2445swap=true := by decide +kernel
theorem fusedMap2445swap_checked : acceptsGraphIso
    (fused (graph core2445) (root 9) 4 0) DegreeTwoThreeSpectrum4446.graph fusedMap2445swap=true := by decide +kernel
theorem certified2445swap : Certified (graph core2445) (root 9) 4 0 :=
  of_native_maps core2445 DegreeTwoThreeSpectrum4818.graph DegreeTwoThreeSpectrum4446.graph
    sourceMap2445swap fusedMap2445swap sourceMap2445swap_checked fusedMap2445swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2445
#print axioms sourceMap2445swap_checked
#print axioms fusedMap2445swap_checked
#print axioms certified2445swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
