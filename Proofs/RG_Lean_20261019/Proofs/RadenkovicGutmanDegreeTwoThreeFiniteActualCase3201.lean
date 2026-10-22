/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3201 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap3201 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3201 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3201_checked : acceptsGraphIso
    (source (graph core3201) (root 8) 0 5) DegreeTwoThreeSpectrum4647.graph sourceMap3201=true := by decide +kernel
theorem fusedMap3201_checked : acceptsGraphIso
    (fused (graph core3201) (root 8) 0 5) DegreeTwoThreeSpectrum4121.graph fusedMap3201=true := by decide +kernel
theorem certified3201 : Certified (graph core3201) (root 8) 0 5 :=
  of_native_maps core3201 DegreeTwoThreeSpectrum4647.graph DegreeTwoThreeSpectrum4121.graph
    sourceMap3201 fusedMap3201 sourceMap3201_checked fusedMap3201_checked
    DegreeTwoThreeFiniteComparisons.comparison3201
#print axioms sourceMap3201_checked
#print axioms fusedMap3201_checked
#print axioms certified3201
def sourceMap3201swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3201swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3201swap_checked : acceptsGraphIso
    (source (graph core3201) (root 8) 5 0) DegreeTwoThreeSpectrum4647.graph sourceMap3201swap=true := by decide +kernel
theorem fusedMap3201swap_checked : acceptsGraphIso
    (fused (graph core3201) (root 8) 5 0) DegreeTwoThreeSpectrum4121.graph fusedMap3201swap=true := by decide +kernel
theorem certified3201swap : Certified (graph core3201) (root 8) 5 0 :=
  of_native_maps core3201 DegreeTwoThreeSpectrum4647.graph DegreeTwoThreeSpectrum4121.graph
    sourceMap3201swap fusedMap3201swap sourceMap3201swap_checked fusedMap3201swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3201
#print axioms sourceMap3201swap_checked
#print axioms fusedMap3201swap_checked
#print axioms certified3201swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
