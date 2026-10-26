/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3838 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap3838 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 8 1 4 v)
def fusedMap3838 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3838_checked : acceptsGraphIso
    (source (graph core3838) (root 8) 1 4) DegreeTwoThreeSpectrum4390.graph sourceMap3838=true := by decide +kernel
theorem fusedMap3838_checked : acceptsGraphIso
    (fused (graph core3838) (root 8) 1 4) DegreeTwoThreeSpectrum3974.graph fusedMap3838=true := by decide +kernel
theorem certified3838 : Certified (graph core3838) (root 8) 1 4 :=
  of_native_maps core3838 DegreeTwoThreeSpectrum4390.graph DegreeTwoThreeSpectrum3974.graph
    sourceMap3838 fusedMap3838 sourceMap3838_checked fusedMap3838_checked
    DegreeTwoThreeFiniteComparisons.comparison3838
#print axioms sourceMap3838_checked
#print axioms fusedMap3838_checked
#print axioms certified3838
def sourceMap3838swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14,15] (sourceLabel 8 4 1 v)
def fusedMap3838swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3838swap_checked : acceptsGraphIso
    (source (graph core3838) (root 8) 4 1) DegreeTwoThreeSpectrum4390.graph sourceMap3838swap=true := by decide +kernel
theorem fusedMap3838swap_checked : acceptsGraphIso
    (fused (graph core3838) (root 8) 4 1) DegreeTwoThreeSpectrum3974.graph fusedMap3838swap=true := by decide +kernel
theorem certified3838swap : Certified (graph core3838) (root 8) 4 1 :=
  of_native_maps core3838 DegreeTwoThreeSpectrum4390.graph DegreeTwoThreeSpectrum3974.graph
    sourceMap3838swap fusedMap3838swap sourceMap3838swap_checked fusedMap3838swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3838
#print axioms sourceMap3838swap_checked
#print axioms fusedMap3838swap_checked
#print axioms certified3838swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
