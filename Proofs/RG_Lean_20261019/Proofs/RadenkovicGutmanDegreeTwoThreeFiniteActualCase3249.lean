/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3249 : Family 9 := level9.get ⟨67,by decide⟩
def sourceMap3249 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 9 0 5 v)
def fusedMap3249 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3249_checked : acceptsGraphIso
    (source (graph core3249) (root 9) 0 5) DegreeTwoThreeSpectrum5420.graph sourceMap3249=true := by decide +kernel
theorem fusedMap3249_checked : acceptsGraphIso
    (fused (graph core3249) (root 9) 0 5) DegreeTwoThreeSpectrum4999.graph fusedMap3249=true := by decide +kernel
theorem certified3249 : Certified (graph core3249) (root 9) 0 5 :=
  of_native_maps core3249 DegreeTwoThreeSpectrum5420.graph DegreeTwoThreeSpectrum4999.graph
    sourceMap3249 fusedMap3249 sourceMap3249_checked fusedMap3249_checked
    DegreeTwoThreeFiniteComparisons.comparison3249
#print axioms sourceMap3249_checked
#print axioms fusedMap3249_checked
#print axioms certified3249
def sourceMap3249swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13,16] (sourceLabel 9 5 0 v)
def fusedMap3249swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3249swap_checked : acceptsGraphIso
    (source (graph core3249) (root 9) 5 0) DegreeTwoThreeSpectrum5420.graph sourceMap3249swap=true := by decide +kernel
theorem fusedMap3249swap_checked : acceptsGraphIso
    (fused (graph core3249) (root 9) 5 0) DegreeTwoThreeSpectrum4999.graph fusedMap3249swap=true := by decide +kernel
theorem certified3249swap : Certified (graph core3249) (root 9) 5 0 :=
  of_native_maps core3249 DegreeTwoThreeSpectrum5420.graph DegreeTwoThreeSpectrum4999.graph
    sourceMap3249swap fusedMap3249swap sourceMap3249swap_checked fusedMap3249swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3249
#print axioms sourceMap3249swap_checked
#print axioms fusedMap3249swap_checked
#print axioms certified3249swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
