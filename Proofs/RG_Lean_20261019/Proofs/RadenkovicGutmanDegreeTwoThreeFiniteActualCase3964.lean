/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3964 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap3964 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3964 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3964_checked : acceptsGraphIso
    (source (graph core3964) (root 7) 1 5) DegreeTwoThreeSpectrum4590.graph sourceMap3964=true := by decide +kernel
theorem fusedMap3964_checked : acceptsGraphIso
    (fused (graph core3964) (root 7) 1 5) DegreeTwoThreeSpectrum4075.graph fusedMap3964=true := by decide +kernel
theorem certified3964 : Certified (graph core3964) (root 7) 1 5 :=
  of_native_maps core3964 DegreeTwoThreeSpectrum4590.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap3964 fusedMap3964 sourceMap3964_checked fusedMap3964_checked
    DegreeTwoThreeFiniteComparisons.comparison3964
#print axioms sourceMap3964_checked
#print axioms fusedMap3964_checked
#print axioms certified3964
def sourceMap3964swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3964swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3964swap_checked : acceptsGraphIso
    (source (graph core3964) (root 7) 5 1) DegreeTwoThreeSpectrum4590.graph sourceMap3964swap=true := by decide +kernel
theorem fusedMap3964swap_checked : acceptsGraphIso
    (fused (graph core3964) (root 7) 5 1) DegreeTwoThreeSpectrum4075.graph fusedMap3964swap=true := by decide +kernel
theorem certified3964swap : Certified (graph core3964) (root 7) 5 1 :=
  of_native_maps core3964 DegreeTwoThreeSpectrum4590.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap3964swap fusedMap3964swap sourceMap3964swap_checked fusedMap3964swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3964
#print axioms sourceMap3964swap_checked
#print axioms fusedMap3964swap_checked
#print axioms certified3964swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
