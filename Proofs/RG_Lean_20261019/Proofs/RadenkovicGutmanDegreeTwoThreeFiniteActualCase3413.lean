/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3413 : Family 9 := level9.get ⟨519,by decide⟩
def sourceMap3413 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3413 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3413_checked : acceptsGraphIso
    (source (graph core3413) (root 9) 0 5) DegreeTwoThreeSpectrum6972.graph sourceMap3413=true := by decide +kernel
theorem fusedMap3413_checked : acceptsGraphIso
    (fused (graph core3413) (root 9) 0 5) DegreeTwoThreeSpectrum5762.graph fusedMap3413=true := by decide +kernel
theorem certified3413 : Certified (graph core3413) (root 9) 0 5 :=
  of_native_maps core3413 DegreeTwoThreeSpectrum6972.graph DegreeTwoThreeSpectrum5762.graph
    sourceMap3413 fusedMap3413 sourceMap3413_checked fusedMap3413_checked
    DegreeTwoThreeFiniteComparisons.comparison3413
#print axioms sourceMap3413_checked
#print axioms fusedMap3413_checked
#print axioms certified3413
def sourceMap3413swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3413swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3413swap_checked : acceptsGraphIso
    (source (graph core3413) (root 9) 5 0) DegreeTwoThreeSpectrum6972.graph sourceMap3413swap=true := by decide +kernel
theorem fusedMap3413swap_checked : acceptsGraphIso
    (fused (graph core3413) (root 9) 5 0) DegreeTwoThreeSpectrum5762.graph fusedMap3413swap=true := by decide +kernel
theorem certified3413swap : Certified (graph core3413) (root 9) 5 0 :=
  of_native_maps core3413 DegreeTwoThreeSpectrum6972.graph DegreeTwoThreeSpectrum5762.graph
    sourceMap3413swap fusedMap3413swap sourceMap3413swap_checked fusedMap3413swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3413
#print axioms sourceMap3413swap_checked
#print axioms fusedMap3413swap_checked
#print axioms certified3413swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
