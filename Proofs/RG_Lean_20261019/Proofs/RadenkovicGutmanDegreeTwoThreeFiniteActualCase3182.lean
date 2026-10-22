/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3182 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap3182 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3182 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3182_checked : acceptsGraphIso
    (source (graph core3182) (root 8) 0 5) DegreeTwoThreeSpectrum4454.graph sourceMap3182=true := by decide +kernel
theorem fusedMap3182_checked : acceptsGraphIso
    (fused (graph core3182) (root 8) 0 5) DegreeTwoThreeSpectrum4002.graph fusedMap3182=true := by decide +kernel
theorem certified3182 : Certified (graph core3182) (root 8) 0 5 :=
  of_native_maps core3182 DegreeTwoThreeSpectrum4454.graph DegreeTwoThreeSpectrum4002.graph
    sourceMap3182 fusedMap3182 sourceMap3182_checked fusedMap3182_checked
    DegreeTwoThreeFiniteComparisons.comparison3182
#print axioms sourceMap3182_checked
#print axioms fusedMap3182_checked
#print axioms certified3182
def sourceMap3182swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3182swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3182swap_checked : acceptsGraphIso
    (source (graph core3182) (root 8) 5 0) DegreeTwoThreeSpectrum4454.graph sourceMap3182swap=true := by decide +kernel
theorem fusedMap3182swap_checked : acceptsGraphIso
    (fused (graph core3182) (root 8) 5 0) DegreeTwoThreeSpectrum4002.graph fusedMap3182swap=true := by decide +kernel
theorem certified3182swap : Certified (graph core3182) (root 8) 5 0 :=
  of_native_maps core3182 DegreeTwoThreeSpectrum4454.graph DegreeTwoThreeSpectrum4002.graph
    sourceMap3182swap fusedMap3182swap sourceMap3182swap_checked fusedMap3182swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3182
#print axioms sourceMap3182swap_checked
#print axioms fusedMap3182swap_checked
#print axioms certified3182swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
