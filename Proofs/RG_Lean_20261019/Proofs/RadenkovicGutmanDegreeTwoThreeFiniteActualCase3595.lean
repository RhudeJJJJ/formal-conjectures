/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3595 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap3595 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3595 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3595_checked : acceptsGraphIso
    (source (graph core3595) (root 8) 0 6) DegreeTwoThreeSpectrum5763.graph sourceMap3595=true := by decide +kernel
theorem fusedMap3595_checked : acceptsGraphIso
    (fused (graph core3595) (root 8) 0 6) DegreeTwoThreeSpectrum5765.graph fusedMap3595=true := by decide +kernel
theorem certified3595 : Certified (graph core3595) (root 8) 0 6 :=
  of_native_maps core3595 DegreeTwoThreeSpectrum5763.graph DegreeTwoThreeSpectrum5765.graph
    sourceMap3595 fusedMap3595 sourceMap3595_checked fusedMap3595_checked
    DegreeTwoThreeFiniteComparisons.comparison3595
#print axioms sourceMap3595_checked
#print axioms fusedMap3595_checked
#print axioms certified3595
def sourceMap3595swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3595swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3595swap_checked : acceptsGraphIso
    (source (graph core3595) (root 8) 6 0) DegreeTwoThreeSpectrum5763.graph sourceMap3595swap=true := by decide +kernel
theorem fusedMap3595swap_checked : acceptsGraphIso
    (fused (graph core3595) (root 8) 6 0) DegreeTwoThreeSpectrum5765.graph fusedMap3595swap=true := by decide +kernel
theorem certified3595swap : Certified (graph core3595) (root 8) 6 0 :=
  of_native_maps core3595 DegreeTwoThreeSpectrum5763.graph DegreeTwoThreeSpectrum5765.graph
    sourceMap3595swap fusedMap3595swap sourceMap3595swap_checked fusedMap3595swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3595
#print axioms sourceMap3595swap_checked
#print axioms fusedMap3595swap_checked
#print axioms certified3595swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
