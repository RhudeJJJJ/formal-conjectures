/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3678 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap3678 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3678 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3678_checked : acceptsGraphIso
    (source (graph core3678) (root 7) 0 7) DegreeTwoThreeSpectrum5771.graph sourceMap3678=true := by decide +kernel
theorem fusedMap3678_checked : acceptsGraphIso
    (fused (graph core3678) (root 7) 0 7) DegreeTwoThreeSpectrum5061.graph fusedMap3678=true := by decide +kernel
theorem certified3678 : Certified (graph core3678) (root 7) 0 7 :=
  of_native_maps core3678 DegreeTwoThreeSpectrum5771.graph DegreeTwoThreeSpectrum5061.graph
    sourceMap3678 fusedMap3678 sourceMap3678_checked fusedMap3678_checked
    DegreeTwoThreeFiniteComparisons.comparison3678
#print axioms sourceMap3678_checked
#print axioms fusedMap3678_checked
#print axioms certified3678
def sourceMap3678swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3678swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3678swap_checked : acceptsGraphIso
    (source (graph core3678) (root 7) 7 0) DegreeTwoThreeSpectrum5771.graph sourceMap3678swap=true := by decide +kernel
theorem fusedMap3678swap_checked : acceptsGraphIso
    (fused (graph core3678) (root 7) 7 0) DegreeTwoThreeSpectrum5061.graph fusedMap3678swap=true := by decide +kernel
theorem certified3678swap : Certified (graph core3678) (root 7) 7 0 :=
  of_native_maps core3678 DegreeTwoThreeSpectrum5771.graph DegreeTwoThreeSpectrum5061.graph
    sourceMap3678swap fusedMap3678swap sourceMap3678swap_checked fusedMap3678swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3678
#print axioms sourceMap3678swap_checked
#print axioms fusedMap3678swap_checked
#print axioms certified3678swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
