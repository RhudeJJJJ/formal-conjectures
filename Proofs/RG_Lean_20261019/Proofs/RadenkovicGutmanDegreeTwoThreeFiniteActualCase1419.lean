/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1419 : Family 9 := level9.get ⟨650,by decide⟩
def sourceMap1419 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1419 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1419_checked : acceptsGraphIso
    (source (graph core1419) (root 9) 0 2) DegreeTwoThreeSpectrum2295.graph sourceMap1419=true := by decide +kernel
theorem fusedMap1419_checked : acceptsGraphIso
    (fused (graph core1419) (root 9) 0 2) DegreeTwoThreeSpectrum2112.graph fusedMap1419=true := by decide +kernel
theorem certified1419 : Certified (graph core1419) (root 9) 0 2 :=
  of_native_maps core1419 DegreeTwoThreeSpectrum2295.graph DegreeTwoThreeSpectrum2112.graph
    sourceMap1419 fusedMap1419 sourceMap1419_checked fusedMap1419_checked
    DegreeTwoThreeFiniteComparisons.comparison1419
#print axioms sourceMap1419_checked
#print axioms fusedMap1419_checked
#print axioms certified1419
def sourceMap1419swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1419swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1419swap_checked : acceptsGraphIso
    (source (graph core1419) (root 9) 2 0) DegreeTwoThreeSpectrum2295.graph sourceMap1419swap=true := by decide +kernel
theorem fusedMap1419swap_checked : acceptsGraphIso
    (fused (graph core1419) (root 9) 2 0) DegreeTwoThreeSpectrum2112.graph fusedMap1419swap=true := by decide +kernel
theorem certified1419swap : Certified (graph core1419) (root 9) 2 0 :=
  of_native_maps core1419 DegreeTwoThreeSpectrum2295.graph DegreeTwoThreeSpectrum2112.graph
    sourceMap1419swap fusedMap1419swap sourceMap1419swap_checked fusedMap1419swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1419
#print axioms sourceMap1419swap_checked
#print axioms fusedMap1419swap_checked
#print axioms certified1419swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
