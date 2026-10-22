/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3520 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap3520 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3520 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3520_checked : acceptsGraphIso
    (source (graph core3520) (root 7) 0 6) DegreeTwoThreeSpectrum4122.graph sourceMap3520=true := by decide +kernel
theorem fusedMap3520_checked : acceptsGraphIso
    (fused (graph core3520) (root 7) 0 6) DegreeTwoThreeSpectrum4124.graph fusedMap3520=true := by decide +kernel
theorem certified3520 : Certified (graph core3520) (root 7) 0 6 :=
  of_native_maps core3520 DegreeTwoThreeSpectrum4122.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap3520 fusedMap3520 sourceMap3520_checked fusedMap3520_checked
    DegreeTwoThreeFiniteComparisons.comparison3520
#print axioms sourceMap3520_checked
#print axioms fusedMap3520_checked
#print axioms certified3520
def sourceMap3520swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3520swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3520swap_checked : acceptsGraphIso
    (source (graph core3520) (root 7) 6 0) DegreeTwoThreeSpectrum4122.graph sourceMap3520swap=true := by decide +kernel
theorem fusedMap3520swap_checked : acceptsGraphIso
    (fused (graph core3520) (root 7) 6 0) DegreeTwoThreeSpectrum4124.graph fusedMap3520swap=true := by decide +kernel
theorem certified3520swap : Certified (graph core3520) (root 7) 6 0 :=
  of_native_maps core3520 DegreeTwoThreeSpectrum4122.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap3520swap fusedMap3520swap sourceMap3520swap_checked fusedMap3520swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3520
#print axioms sourceMap3520swap_checked
#print axioms fusedMap3520swap_checked
#print axioms certified3520swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
