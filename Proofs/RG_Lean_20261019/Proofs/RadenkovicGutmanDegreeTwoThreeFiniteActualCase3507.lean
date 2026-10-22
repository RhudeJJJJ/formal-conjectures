/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3507 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap3507 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3507 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3507_checked : acceptsGraphIso
    (source (graph core3507) (root 7) 0 6) DegreeTwoThreeSpectrum4160.graph sourceMap3507=true := by decide +kernel
theorem fusedMap3507_checked : acceptsGraphIso
    (fused (graph core3507) (root 7) 0 6) DegreeTwoThreeSpectrum3883.graph fusedMap3507=true := by decide +kernel
theorem certified3507 : Certified (graph core3507) (root 7) 0 6 :=
  of_native_maps core3507 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap3507 fusedMap3507 sourceMap3507_checked fusedMap3507_checked
    DegreeTwoThreeFiniteComparisons.comparison3507
#print axioms sourceMap3507_checked
#print axioms fusedMap3507_checked
#print axioms certified3507
def sourceMap3507swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3507swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3507swap_checked : acceptsGraphIso
    (source (graph core3507) (root 7) 6 0) DegreeTwoThreeSpectrum4160.graph sourceMap3507swap=true := by decide +kernel
theorem fusedMap3507swap_checked : acceptsGraphIso
    (fused (graph core3507) (root 7) 6 0) DegreeTwoThreeSpectrum3883.graph fusedMap3507swap=true := by decide +kernel
theorem certified3507swap : Certified (graph core3507) (root 7) 6 0 :=
  of_native_maps core3507 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap3507swap fusedMap3507swap sourceMap3507swap_checked fusedMap3507swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3507
#print axioms sourceMap3507swap_checked
#print axioms fusedMap3507swap_checked
#print axioms certified3507swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
