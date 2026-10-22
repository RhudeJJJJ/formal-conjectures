/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3220 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap3220 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3220 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3220_checked : acceptsGraphIso
    (source (graph core3220) (root 8) 0 5) DegreeTwoThreeSpectrum4393.graph sourceMap3220=true := by decide +kernel
theorem fusedMap3220_checked : acceptsGraphIso
    (fused (graph core3220) (root 8) 0 5) DegreeTwoThreeSpectrum4394.graph fusedMap3220=true := by decide +kernel
theorem certified3220 : Certified (graph core3220) (root 8) 0 5 :=
  of_native_maps core3220 DegreeTwoThreeSpectrum4393.graph DegreeTwoThreeSpectrum4394.graph
    sourceMap3220 fusedMap3220 sourceMap3220_checked fusedMap3220_checked
    DegreeTwoThreeFiniteComparisons.comparison3220
#print axioms sourceMap3220_checked
#print axioms fusedMap3220_checked
#print axioms certified3220
def sourceMap3220swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3220swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3220swap_checked : acceptsGraphIso
    (source (graph core3220) (root 8) 5 0) DegreeTwoThreeSpectrum4393.graph sourceMap3220swap=true := by decide +kernel
theorem fusedMap3220swap_checked : acceptsGraphIso
    (fused (graph core3220) (root 8) 5 0) DegreeTwoThreeSpectrum4394.graph fusedMap3220swap=true := by decide +kernel
theorem certified3220swap : Certified (graph core3220) (root 8) 5 0 :=
  of_native_maps core3220 DegreeTwoThreeSpectrum4393.graph DegreeTwoThreeSpectrum4394.graph
    sourceMap3220swap fusedMap3220swap sourceMap3220swap_checked fusedMap3220swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3220
#print axioms sourceMap3220swap_checked
#print axioms fusedMap3220swap_checked
#print axioms certified3220swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
