/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3661 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3661 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3661 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3661_checked : acceptsGraphIso
    (source (graph core3661) (root 6) 0 7) DegreeTwoThreeSpectrum4261.graph sourceMap3661=true := by decide +kernel
theorem fusedMap3661_checked : acceptsGraphIso
    (fused (graph core3661) (root 6) 0 7) DegreeTwoThreeSpectrum3917.graph fusedMap3661=true := by decide +kernel
theorem certified3661 : Certified (graph core3661) (root 6) 0 7 :=
  of_native_maps core3661 DegreeTwoThreeSpectrum4261.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap3661 fusedMap3661 sourceMap3661_checked fusedMap3661_checked
    DegreeTwoThreeFiniteComparisons.comparison3661
#print axioms sourceMap3661_checked
#print axioms fusedMap3661_checked
#print axioms certified3661
def sourceMap3661swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,10] (sourceLabel 6 7 0 v)
def fusedMap3661swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3661swap_checked : acceptsGraphIso
    (source (graph core3661) (root 6) 7 0) DegreeTwoThreeSpectrum4261.graph sourceMap3661swap=true := by decide +kernel
theorem fusedMap3661swap_checked : acceptsGraphIso
    (fused (graph core3661) (root 6) 7 0) DegreeTwoThreeSpectrum3917.graph fusedMap3661swap=true := by decide +kernel
theorem certified3661swap : Certified (graph core3661) (root 6) 7 0 :=
  of_native_maps core3661 DegreeTwoThreeSpectrum4261.graph DegreeTwoThreeSpectrum3917.graph
    sourceMap3661swap fusedMap3661swap sourceMap3661swap_checked fusedMap3661swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3661
#print axioms sourceMap3661swap_checked
#print axioms fusedMap3661swap_checked
#print axioms certified3661swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
