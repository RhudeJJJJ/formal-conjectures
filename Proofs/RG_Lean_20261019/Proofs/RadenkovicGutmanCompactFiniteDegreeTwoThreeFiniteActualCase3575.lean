/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3575 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap3575 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3575 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3575_checked : acceptsGraphIso
    (source (graph core3575) (root 8) 0 6) DegreeTwoThreeSpectrum5341.graph sourceMap3575=true := by decide +kernel
theorem fusedMap3575_checked : acceptsGraphIso
    (fused (graph core3575) (root 8) 0 6) DegreeTwoThreeSpectrum5343.graph fusedMap3575=true := by decide +kernel
theorem certified3575 : Certified (graph core3575) (root 8) 0 6 :=
  of_native_maps core3575 DegreeTwoThreeSpectrum5341.graph DegreeTwoThreeSpectrum5343.graph
    sourceMap3575 fusedMap3575 sourceMap3575_checked fusedMap3575_checked
    DegreeTwoThreeFiniteComparisons.comparison3575
#print axioms sourceMap3575_checked
#print axioms fusedMap3575_checked
#print axioms certified3575
def sourceMap3575swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3575swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3575swap_checked : acceptsGraphIso
    (source (graph core3575) (root 8) 6 0) DegreeTwoThreeSpectrum5341.graph sourceMap3575swap=true := by decide +kernel
theorem fusedMap3575swap_checked : acceptsGraphIso
    (fused (graph core3575) (root 8) 6 0) DegreeTwoThreeSpectrum5343.graph fusedMap3575swap=true := by decide +kernel
theorem certified3575swap : Certified (graph core3575) (root 8) 6 0 :=
  of_native_maps core3575 DegreeTwoThreeSpectrum5341.graph DegreeTwoThreeSpectrum5343.graph
    sourceMap3575swap fusedMap3575swap sourceMap3575swap_checked fusedMap3575swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3575
#print axioms sourceMap3575swap_checked
#print axioms fusedMap3575swap_checked
#print axioms certified3575swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
