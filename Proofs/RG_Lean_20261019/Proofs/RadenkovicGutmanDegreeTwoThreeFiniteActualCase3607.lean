/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3607 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap3607 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3607 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3607_checked : acceptsGraphIso
    (source (graph core3607) (root 8) 0 6) DegreeTwoThreeSpectrum6123.graph sourceMap3607=true := by decide +kernel
theorem fusedMap3607_checked : acceptsGraphIso
    (fused (graph core3607) (root 8) 0 6) DegreeTwoThreeSpectrum5183.graph fusedMap3607=true := by decide +kernel
theorem certified3607 : Certified (graph core3607) (root 8) 0 6 :=
  of_native_maps core3607 DegreeTwoThreeSpectrum6123.graph DegreeTwoThreeSpectrum5183.graph
    sourceMap3607 fusedMap3607 sourceMap3607_checked fusedMap3607_checked
    DegreeTwoThreeFiniteComparisons.comparison3607
#print axioms sourceMap3607_checked
#print axioms fusedMap3607_checked
#print axioms certified3607
def sourceMap3607swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3607swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3607swap_checked : acceptsGraphIso
    (source (graph core3607) (root 8) 6 0) DegreeTwoThreeSpectrum6123.graph sourceMap3607swap=true := by decide +kernel
theorem fusedMap3607swap_checked : acceptsGraphIso
    (fused (graph core3607) (root 8) 6 0) DegreeTwoThreeSpectrum5183.graph fusedMap3607swap=true := by decide +kernel
theorem certified3607swap : Certified (graph core3607) (root 8) 6 0 :=
  of_native_maps core3607 DegreeTwoThreeSpectrum6123.graph DegreeTwoThreeSpectrum5183.graph
    sourceMap3607swap fusedMap3607swap sourceMap3607swap_checked fusedMap3607swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3607
#print axioms sourceMap3607swap_checked
#print axioms fusedMap3607swap_checked
#print axioms certified3607swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
