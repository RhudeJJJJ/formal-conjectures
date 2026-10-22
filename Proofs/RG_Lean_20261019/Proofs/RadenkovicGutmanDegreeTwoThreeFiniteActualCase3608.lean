/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3608 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap3608 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3608 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3608_checked : acceptsGraphIso
    (source (graph core3608) (root 8) 0 6) DegreeTwoThreeSpectrum6129.graph sourceMap3608=true := by decide +kernel
theorem fusedMap3608_checked : acceptsGraphIso
    (fused (graph core3608) (root 8) 0 6) DegreeTwoThreeSpectrum5184.graph fusedMap3608=true := by decide +kernel
theorem certified3608 : Certified (graph core3608) (root 8) 0 6 :=
  of_native_maps core3608 DegreeTwoThreeSpectrum6129.graph DegreeTwoThreeSpectrum5184.graph
    sourceMap3608 fusedMap3608 sourceMap3608_checked fusedMap3608_checked
    DegreeTwoThreeFiniteComparisons.comparison3608
#print axioms sourceMap3608_checked
#print axioms fusedMap3608_checked
#print axioms certified3608
def sourceMap3608swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3608swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3608swap_checked : acceptsGraphIso
    (source (graph core3608) (root 8) 6 0) DegreeTwoThreeSpectrum6129.graph sourceMap3608swap=true := by decide +kernel
theorem fusedMap3608swap_checked : acceptsGraphIso
    (fused (graph core3608) (root 8) 6 0) DegreeTwoThreeSpectrum5184.graph fusedMap3608swap=true := by decide +kernel
theorem certified3608swap : Certified (graph core3608) (root 8) 6 0 :=
  of_native_maps core3608 DegreeTwoThreeSpectrum6129.graph DegreeTwoThreeSpectrum5184.graph
    sourceMap3608swap fusedMap3608swap sourceMap3608swap_checked fusedMap3608swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3608
#print axioms sourceMap3608swap_checked
#print axioms fusedMap3608swap_checked
#print axioms certified3608swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
