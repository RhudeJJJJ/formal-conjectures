/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3717 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3717 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3717 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3717_checked : acceptsGraphIso
    (source (graph core3717) (root 6) 0 8) DegreeTwoThreeSpectrum5318.graph sourceMap3717=true := by decide +kernel
theorem fusedMap3717_checked : acceptsGraphIso
    (fused (graph core3717) (root 6) 0 8) DegreeTwoThreeSpectrum4981.graph fusedMap3717=true := by decide +kernel
theorem certified3717 : Certified (graph core3717) (root 6) 0 8 :=
  of_native_maps core3717 DegreeTwoThreeSpectrum5318.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap3717 fusedMap3717 sourceMap3717_checked fusedMap3717_checked
    DegreeTwoThreeFiniteComparisons.comparison3717
#print axioms sourceMap3717_checked
#print axioms fusedMap3717_checked
#print axioms certified3717
def sourceMap3717swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3717swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3717swap_checked : acceptsGraphIso
    (source (graph core3717) (root 6) 8 0) DegreeTwoThreeSpectrum5318.graph sourceMap3717swap=true := by decide +kernel
theorem fusedMap3717swap_checked : acceptsGraphIso
    (fused (graph core3717) (root 6) 8 0) DegreeTwoThreeSpectrum4981.graph fusedMap3717swap=true := by decide +kernel
theorem certified3717swap : Certified (graph core3717) (root 6) 8 0 :=
  of_native_maps core3717 DegreeTwoThreeSpectrum5318.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap3717swap fusedMap3717swap sourceMap3717swap_checked fusedMap3717swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3717
#print axioms sourceMap3717swap_checked
#print axioms fusedMap3717swap_checked
#print axioms certified3717swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
