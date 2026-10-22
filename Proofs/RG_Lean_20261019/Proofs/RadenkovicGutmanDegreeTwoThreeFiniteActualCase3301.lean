/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3301 : Family 9 := level9.get ⟨242,by decide⟩
def sourceMap3301 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3301 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3301_checked : acceptsGraphIso
    (source (graph core3301) (root 9) 0 5) DegreeTwoThreeSpectrum5609.graph sourceMap3301=true := by decide +kernel
theorem fusedMap3301_checked : acceptsGraphIso
    (fused (graph core3301) (root 9) 0 5) DegreeTwoThreeSpectrum5610.graph fusedMap3301=true := by decide +kernel
theorem certified3301 : Certified (graph core3301) (root 9) 0 5 :=
  of_native_maps core3301 DegreeTwoThreeSpectrum5609.graph DegreeTwoThreeSpectrum5610.graph
    sourceMap3301 fusedMap3301 sourceMap3301_checked fusedMap3301_checked
    DegreeTwoThreeFiniteComparisons.comparison3301
#print axioms sourceMap3301_checked
#print axioms fusedMap3301_checked
#print axioms certified3301
def sourceMap3301swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3301swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3301swap_checked : acceptsGraphIso
    (source (graph core3301) (root 9) 5 0) DegreeTwoThreeSpectrum5609.graph sourceMap3301swap=true := by decide +kernel
theorem fusedMap3301swap_checked : acceptsGraphIso
    (fused (graph core3301) (root 9) 5 0) DegreeTwoThreeSpectrum5610.graph fusedMap3301swap=true := by decide +kernel
theorem certified3301swap : Certified (graph core3301) (root 9) 5 0 :=
  of_native_maps core3301 DegreeTwoThreeSpectrum5609.graph DegreeTwoThreeSpectrum5610.graph
    sourceMap3301swap fusedMap3301swap sourceMap3301swap_checked fusedMap3301swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3301
#print axioms sourceMap3301swap_checked
#print axioms fusedMap3301swap_checked
#print axioms certified3301swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
