/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3707 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3707 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3707 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3707_checked : acceptsGraphIso
    (source (graph core3707) (root 5) 0 8) DegreeTwoThreeSpectrum4071.graph sourceMap3707=true := by decide +kernel
theorem fusedMap3707_checked : acceptsGraphIso
    (fused (graph core3707) (root 5) 0 8) DegreeTwoThreeSpectrum3870.graph fusedMap3707=true := by decide +kernel
theorem certified3707 : Certified (graph core3707) (root 5) 0 8 :=
  of_native_maps core3707 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap3707 fusedMap3707 sourceMap3707_checked fusedMap3707_checked
    DegreeTwoThreeFiniteComparisons.comparison3707
#print axioms sourceMap3707_checked
#print axioms fusedMap3707_checked
#print axioms certified3707
def sourceMap3707swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,9] (sourceLabel 5 8 0 v)
def fusedMap3707swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3707swap_checked : acceptsGraphIso
    (source (graph core3707) (root 5) 8 0) DegreeTwoThreeSpectrum4071.graph sourceMap3707swap=true := by decide +kernel
theorem fusedMap3707swap_checked : acceptsGraphIso
    (fused (graph core3707) (root 5) 8 0) DegreeTwoThreeSpectrum3870.graph fusedMap3707swap=true := by decide +kernel
theorem certified3707swap : Certified (graph core3707) (root 5) 8 0 :=
  of_native_maps core3707 DegreeTwoThreeSpectrum4071.graph DegreeTwoThreeSpectrum3870.graph
    sourceMap3707swap fusedMap3707swap sourceMap3707swap_checked fusedMap3707swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3707
#print axioms sourceMap3707swap_checked
#print axioms fusedMap3707swap_checked
#print axioms certified3707swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
