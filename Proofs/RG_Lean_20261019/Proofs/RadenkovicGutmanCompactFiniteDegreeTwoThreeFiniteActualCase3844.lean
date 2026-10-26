/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3844 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap3844 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3844 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3844_checked : acceptsGraphIso
    (source (graph core3844) (root 8) 1 4) DegreeTwoThreeSpectrum4592.graph sourceMap3844=true := by decide +kernel
theorem fusedMap3844_checked : acceptsGraphIso
    (fused (graph core3844) (root 8) 1 4) DegreeTwoThreeSpectrum4078.graph fusedMap3844=true := by decide +kernel
theorem certified3844 : Certified (graph core3844) (root 8) 1 4 :=
  of_native_maps core3844 DegreeTwoThreeSpectrum4592.graph DegreeTwoThreeSpectrum4078.graph
    sourceMap3844 fusedMap3844 sourceMap3844_checked fusedMap3844_checked
    DegreeTwoThreeFiniteComparisons.comparison3844
#print axioms sourceMap3844_checked
#print axioms fusedMap3844_checked
#print axioms certified3844
def sourceMap3844swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3844swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3844swap_checked : acceptsGraphIso
    (source (graph core3844) (root 8) 4 1) DegreeTwoThreeSpectrum4592.graph sourceMap3844swap=true := by decide +kernel
theorem fusedMap3844swap_checked : acceptsGraphIso
    (fused (graph core3844) (root 8) 4 1) DegreeTwoThreeSpectrum4078.graph fusedMap3844swap=true := by decide +kernel
theorem certified3844swap : Certified (graph core3844) (root 8) 4 1 :=
  of_native_maps core3844 DegreeTwoThreeSpectrum4592.graph DegreeTwoThreeSpectrum4078.graph
    sourceMap3844swap fusedMap3844swap sourceMap3844swap_checked fusedMap3844swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3844
#print axioms sourceMap3844swap_checked
#print axioms fusedMap3844swap_checked
#print axioms certified3844swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
