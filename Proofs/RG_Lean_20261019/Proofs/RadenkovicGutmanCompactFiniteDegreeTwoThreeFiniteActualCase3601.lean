/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3601 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap3601 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3601 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3601_checked : acceptsGraphIso
    (source (graph core3601) (root 8) 0 6) DegreeTwoThreeSpectrum5986.graph sourceMap3601=true := by decide +kernel
theorem fusedMap3601_checked : acceptsGraphIso
    (fused (graph core3601) (root 8) 0 6) DegreeTwoThreeSpectrum5136.graph fusedMap3601=true := by decide +kernel
theorem certified3601 : Certified (graph core3601) (root 8) 0 6 :=
  of_native_maps core3601 DegreeTwoThreeSpectrum5986.graph DegreeTwoThreeSpectrum5136.graph
    sourceMap3601 fusedMap3601 sourceMap3601_checked fusedMap3601_checked
    DegreeTwoThreeFiniteComparisons.comparison3601
#print axioms sourceMap3601_checked
#print axioms fusedMap3601_checked
#print axioms certified3601
def sourceMap3601swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3601swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3601swap_checked : acceptsGraphIso
    (source (graph core3601) (root 8) 6 0) DegreeTwoThreeSpectrum5986.graph sourceMap3601swap=true := by decide +kernel
theorem fusedMap3601swap_checked : acceptsGraphIso
    (fused (graph core3601) (root 8) 6 0) DegreeTwoThreeSpectrum5136.graph fusedMap3601swap=true := by decide +kernel
theorem certified3601swap : Certified (graph core3601) (root 8) 6 0 :=
  of_native_maps core3601 DegreeTwoThreeSpectrum5986.graph DegreeTwoThreeSpectrum5136.graph
    sourceMap3601swap fusedMap3601swap sourceMap3601swap_checked fusedMap3601swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3601
#print axioms sourceMap3601swap_checked
#print axioms fusedMap3601swap_checked
#print axioms certified3601swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
