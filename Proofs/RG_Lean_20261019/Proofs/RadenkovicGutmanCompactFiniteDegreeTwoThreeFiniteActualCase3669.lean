/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3669 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap3669 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3669 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3669_checked : acceptsGraphIso
    (source (graph core3669) (root 7) 0 7) DegreeTwoThreeSpectrum5288.graph sourceMap3669=true := by decide +kernel
theorem fusedMap3669_checked : acceptsGraphIso
    (fused (graph core3669) (root 7) 0 7) DegreeTwoThreeSpectrum4976.graph fusedMap3669=true := by decide +kernel
theorem certified3669 : Certified (graph core3669) (root 7) 0 7 :=
  of_native_maps core3669 DegreeTwoThreeSpectrum5288.graph DegreeTwoThreeSpectrum4976.graph
    sourceMap3669 fusedMap3669 sourceMap3669_checked fusedMap3669_checked
    DegreeTwoThreeFiniteComparisons.comparison3669
#print axioms sourceMap3669_checked
#print axioms fusedMap3669_checked
#print axioms certified3669
def sourceMap3669swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3669swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3669swap_checked : acceptsGraphIso
    (source (graph core3669) (root 7) 7 0) DegreeTwoThreeSpectrum5288.graph sourceMap3669swap=true := by decide +kernel
theorem fusedMap3669swap_checked : acceptsGraphIso
    (fused (graph core3669) (root 7) 7 0) DegreeTwoThreeSpectrum4976.graph fusedMap3669swap=true := by decide +kernel
theorem certified3669swap : Certified (graph core3669) (root 7) 7 0 :=
  of_native_maps core3669 DegreeTwoThreeSpectrum5288.graph DegreeTwoThreeSpectrum4976.graph
    sourceMap3669swap fusedMap3669swap sourceMap3669swap_checked fusedMap3669swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3669
#print axioms sourceMap3669swap_checked
#print axioms fusedMap3669swap_checked
#print axioms certified3669swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
