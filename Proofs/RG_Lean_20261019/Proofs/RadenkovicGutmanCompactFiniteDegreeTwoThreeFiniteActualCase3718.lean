/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3718 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap3718 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3718 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3718_checked : acceptsGraphIso
    (source (graph core3718) (root 6) 0 8) DegreeTwoThreeSpectrum5449.graph sourceMap3718=true := by decide +kernel
theorem fusedMap3718_checked : acceptsGraphIso
    (fused (graph core3718) (root 6) 0 8) DegreeTwoThreeSpectrum5009.graph fusedMap3718=true := by decide +kernel
theorem certified3718 : Certified (graph core3718) (root 6) 0 8 :=
  of_native_maps core3718 DegreeTwoThreeSpectrum5449.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap3718 fusedMap3718 sourceMap3718_checked fusedMap3718_checked
    DegreeTwoThreeFiniteComparisons.comparison3718
#print axioms sourceMap3718_checked
#print axioms fusedMap3718_checked
#print axioms certified3718
def sourceMap3718swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3718swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3718swap_checked : acceptsGraphIso
    (source (graph core3718) (root 6) 8 0) DegreeTwoThreeSpectrum5449.graph sourceMap3718swap=true := by decide +kernel
theorem fusedMap3718swap_checked : acceptsGraphIso
    (fused (graph core3718) (root 6) 8 0) DegreeTwoThreeSpectrum5009.graph fusedMap3718swap=true := by decide +kernel
theorem certified3718swap : Certified (graph core3718) (root 6) 8 0 :=
  of_native_maps core3718 DegreeTwoThreeSpectrum5449.graph DegreeTwoThreeSpectrum5009.graph
    sourceMap3718swap fusedMap3718swap sourceMap3718swap_checked fusedMap3718swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3718
#print axioms sourceMap3718swap_checked
#print axioms fusedMap3718swap_checked
#print axioms certified3718swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
