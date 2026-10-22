/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3404 : Family 9 := level9.get ⟨503,by decide⟩
def sourceMap3404 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3404 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3404_checked : acceptsGraphIso
    (source (graph core3404) (root 9) 0 5) DegreeTwoThreeSpectrum6912.graph sourceMap3404=true := by decide +kernel
theorem fusedMap3404_checked : acceptsGraphIso
    (fused (graph core3404) (root 9) 0 5) DegreeTwoThreeSpectrum5694.graph fusedMap3404=true := by decide +kernel
theorem certified3404 : Certified (graph core3404) (root 9) 0 5 :=
  of_native_maps core3404 DegreeTwoThreeSpectrum6912.graph DegreeTwoThreeSpectrum5694.graph
    sourceMap3404 fusedMap3404 sourceMap3404_checked fusedMap3404_checked
    DegreeTwoThreeFiniteComparisons.comparison3404
#print axioms sourceMap3404_checked
#print axioms fusedMap3404_checked
#print axioms certified3404
def sourceMap3404swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3404swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3404swap_checked : acceptsGraphIso
    (source (graph core3404) (root 9) 5 0) DegreeTwoThreeSpectrum6912.graph sourceMap3404swap=true := by decide +kernel
theorem fusedMap3404swap_checked : acceptsGraphIso
    (fused (graph core3404) (root 9) 5 0) DegreeTwoThreeSpectrum5694.graph fusedMap3404swap=true := by decide +kernel
theorem certified3404swap : Certified (graph core3404) (root 9) 5 0 :=
  of_native_maps core3404 DegreeTwoThreeSpectrum6912.graph DegreeTwoThreeSpectrum5694.graph
    sourceMap3404swap fusedMap3404swap sourceMap3404swap_checked fusedMap3404swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3404
#print axioms sourceMap3404swap_checked
#print axioms fusedMap3404swap_checked
#print axioms certified3404swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
