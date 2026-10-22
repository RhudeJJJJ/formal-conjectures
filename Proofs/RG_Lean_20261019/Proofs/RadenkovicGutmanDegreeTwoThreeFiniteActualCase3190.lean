/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3190 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap3190 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3190 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3190_checked : acceptsGraphIso
    (source (graph core3190) (root 8) 0 5) DegreeTwoThreeSpectrum4560.graph sourceMap3190=true := by decide +kernel
theorem fusedMap3190_checked : acceptsGraphIso
    (fused (graph core3190) (root 8) 0 5) DegreeTwoThreeSpectrum4060.graph fusedMap3190=true := by decide +kernel
theorem certified3190 : Certified (graph core3190) (root 8) 0 5 :=
  of_native_maps core3190 DegreeTwoThreeSpectrum4560.graph DegreeTwoThreeSpectrum4060.graph
    sourceMap3190 fusedMap3190 sourceMap3190_checked fusedMap3190_checked
    DegreeTwoThreeFiniteComparisons.comparison3190
#print axioms sourceMap3190_checked
#print axioms fusedMap3190_checked
#print axioms certified3190
def sourceMap3190swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3190swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3190swap_checked : acceptsGraphIso
    (source (graph core3190) (root 8) 5 0) DegreeTwoThreeSpectrum4560.graph sourceMap3190swap=true := by decide +kernel
theorem fusedMap3190swap_checked : acceptsGraphIso
    (fused (graph core3190) (root 8) 5 0) DegreeTwoThreeSpectrum4060.graph fusedMap3190swap=true := by decide +kernel
theorem certified3190swap : Certified (graph core3190) (root 8) 5 0 :=
  of_native_maps core3190 DegreeTwoThreeSpectrum4560.graph DegreeTwoThreeSpectrum4060.graph
    sourceMap3190swap fusedMap3190swap sourceMap3190swap_checked fusedMap3190swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3190
#print axioms sourceMap3190swap_checked
#print axioms fusedMap3190swap_checked
#print axioms certified3190swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
