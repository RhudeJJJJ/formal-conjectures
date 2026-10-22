/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3225 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap3225 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3225 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3225_checked : acceptsGraphIso
    (source (graph core3225) (root 8) 0 5) DegreeTwoThreeSpectrum4441.graph sourceMap3225=true := by decide +kernel
theorem fusedMap3225_checked : acceptsGraphIso
    (fused (graph core3225) (root 8) 0 5) DegreeTwoThreeSpectrum4442.graph fusedMap3225=true := by decide +kernel
theorem certified3225 : Certified (graph core3225) (root 8) 0 5 :=
  of_native_maps core3225 DegreeTwoThreeSpectrum4441.graph DegreeTwoThreeSpectrum4442.graph
    sourceMap3225 fusedMap3225 sourceMap3225_checked fusedMap3225_checked
    DegreeTwoThreeFiniteComparisons.comparison3225
#print axioms sourceMap3225_checked
#print axioms fusedMap3225_checked
#print axioms certified3225
def sourceMap3225swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3225swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3225swap_checked : acceptsGraphIso
    (source (graph core3225) (root 8) 5 0) DegreeTwoThreeSpectrum4441.graph sourceMap3225swap=true := by decide +kernel
theorem fusedMap3225swap_checked : acceptsGraphIso
    (fused (graph core3225) (root 8) 5 0) DegreeTwoThreeSpectrum4442.graph fusedMap3225swap=true := by decide +kernel
theorem certified3225swap : Certified (graph core3225) (root 8) 5 0 :=
  of_native_maps core3225 DegreeTwoThreeSpectrum4441.graph DegreeTwoThreeSpectrum4442.graph
    sourceMap3225swap fusedMap3225swap sourceMap3225swap_checked fusedMap3225swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3225
#print axioms sourceMap3225swap_checked
#print axioms fusedMap3225swap_checked
#print axioms certified3225swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
