/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3206 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap3206 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3206 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3206_checked : acceptsGraphIso
    (source (graph core3206) (root 8) 0 5) DegreeTwoThreeSpectrum4218.graph sourceMap3206=true := by decide +kernel
theorem fusedMap3206_checked : acceptsGraphIso
    (fused (graph core3206) (root 8) 0 5) DegreeTwoThreeSpectrum4219.graph fusedMap3206=true := by decide +kernel
theorem certified3206 : Certified (graph core3206) (root 8) 0 5 :=
  of_native_maps core3206 DegreeTwoThreeSpectrum4218.graph DegreeTwoThreeSpectrum4219.graph
    sourceMap3206 fusedMap3206 sourceMap3206_checked fusedMap3206_checked
    DegreeTwoThreeFiniteComparisons.comparison3206
#print axioms sourceMap3206_checked
#print axioms fusedMap3206_checked
#print axioms certified3206
def sourceMap3206swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3206swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3206swap_checked : acceptsGraphIso
    (source (graph core3206) (root 8) 5 0) DegreeTwoThreeSpectrum4218.graph sourceMap3206swap=true := by decide +kernel
theorem fusedMap3206swap_checked : acceptsGraphIso
    (fused (graph core3206) (root 8) 5 0) DegreeTwoThreeSpectrum4219.graph fusedMap3206swap=true := by decide +kernel
theorem certified3206swap : Certified (graph core3206) (root 8) 5 0 :=
  of_native_maps core3206 DegreeTwoThreeSpectrum4218.graph DegreeTwoThreeSpectrum4219.graph
    sourceMap3206swap fusedMap3206swap sourceMap3206swap_checked fusedMap3206swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3206
#print axioms sourceMap3206swap_checked
#print axioms fusedMap3206swap_checked
#print axioms certified3206swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
