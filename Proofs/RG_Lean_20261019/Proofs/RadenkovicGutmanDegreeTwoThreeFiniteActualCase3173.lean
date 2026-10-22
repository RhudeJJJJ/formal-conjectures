/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3173 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap3173 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3173 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3173_checked : acceptsGraphIso
    (source (graph core3173) (root 8) 0 5) DegreeTwoThreeSpectrum4325.graph sourceMap3173=true := by decide +kernel
theorem fusedMap3173_checked : acceptsGraphIso
    (fused (graph core3173) (root 8) 0 5) DegreeTwoThreeSpectrum3932.graph fusedMap3173=true := by decide +kernel
theorem certified3173 : Certified (graph core3173) (root 8) 0 5 :=
  of_native_maps core3173 DegreeTwoThreeSpectrum4325.graph DegreeTwoThreeSpectrum3932.graph
    sourceMap3173 fusedMap3173 sourceMap3173_checked fusedMap3173_checked
    DegreeTwoThreeFiniteComparisons.comparison3173
#print axioms sourceMap3173_checked
#print axioms fusedMap3173_checked
#print axioms certified3173
def sourceMap3173swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3173swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3173swap_checked : acceptsGraphIso
    (source (graph core3173) (root 8) 5 0) DegreeTwoThreeSpectrum4325.graph sourceMap3173swap=true := by decide +kernel
theorem fusedMap3173swap_checked : acceptsGraphIso
    (fused (graph core3173) (root 8) 5 0) DegreeTwoThreeSpectrum3932.graph fusedMap3173swap=true := by decide +kernel
theorem certified3173swap : Certified (graph core3173) (root 8) 5 0 :=
  of_native_maps core3173 DegreeTwoThreeSpectrum4325.graph DegreeTwoThreeSpectrum3932.graph
    sourceMap3173swap fusedMap3173swap sourceMap3173swap_checked fusedMap3173swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3173
#print axioms sourceMap3173swap_checked
#print axioms fusedMap3173swap_checked
#print axioms certified3173swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
