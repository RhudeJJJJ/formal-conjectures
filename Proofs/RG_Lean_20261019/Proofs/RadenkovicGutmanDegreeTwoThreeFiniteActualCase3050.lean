/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3050 : Family 10 := level10.get ⟨1705,by decide⟩
def sourceMap3050 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3050 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3050_checked : acceptsGraphIso
    (source (graph core3050) (root 10) 0 4) DegreeTwoThreeSpectrum7326.graph sourceMap3050=true := by decide +kernel
theorem fusedMap3050_checked : acceptsGraphIso
    (fused (graph core3050) (root 10) 0 4) DegreeTwoThreeSpectrum6475.graph fusedMap3050=true := by decide +kernel
theorem certified3050 : Certified (graph core3050) (root 10) 0 4 :=
  of_native_maps core3050 DegreeTwoThreeSpectrum7326.graph DegreeTwoThreeSpectrum6475.graph
    sourceMap3050 fusedMap3050 sourceMap3050_checked fusedMap3050_checked
    DegreeTwoThreeFiniteComparisons.comparison3050
#print axioms sourceMap3050_checked
#print axioms fusedMap3050_checked
#print axioms certified3050
def sourceMap3050swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3050swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3050swap_checked : acceptsGraphIso
    (source (graph core3050) (root 10) 4 0) DegreeTwoThreeSpectrum7326.graph sourceMap3050swap=true := by decide +kernel
theorem fusedMap3050swap_checked : acceptsGraphIso
    (fused (graph core3050) (root 10) 4 0) DegreeTwoThreeSpectrum6475.graph fusedMap3050swap=true := by decide +kernel
theorem certified3050swap : Certified (graph core3050) (root 10) 4 0 :=
  of_native_maps core3050 DegreeTwoThreeSpectrum7326.graph DegreeTwoThreeSpectrum6475.graph
    sourceMap3050swap fusedMap3050swap sourceMap3050swap_checked fusedMap3050swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3050
#print axioms sourceMap3050swap_checked
#print axioms fusedMap3050swap_checked
#print axioms certified3050swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
