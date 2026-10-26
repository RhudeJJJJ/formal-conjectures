/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3704 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3704 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3704 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3704_checked : acceptsGraphIso
    (source (graph core3704) (root 5) 0 8) DegreeTwoThreeSpectrum3878.graph sourceMap3704=true := by decide +kernel
theorem fusedMap3704_checked : acceptsGraphIso
    (fused (graph core3704) (root 5) 0 8) DegreeTwoThreeSpectrum3882.graph fusedMap3704=true := by decide +kernel
theorem certified3704 : Certified (graph core3704) (root 5) 0 8 :=
  of_native_maps core3704 DegreeTwoThreeSpectrum3878.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap3704 fusedMap3704 sourceMap3704_checked fusedMap3704_checked
    DegreeTwoThreeFiniteComparisons.comparison3704
#print axioms sourceMap3704_checked
#print axioms fusedMap3704_checked
#print axioms certified3704
def sourceMap3704swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,14,15,8] (sourceLabel 5 8 0 v)
def fusedMap3704swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3704swap_checked : acceptsGraphIso
    (source (graph core3704) (root 5) 8 0) DegreeTwoThreeSpectrum3878.graph sourceMap3704swap=true := by decide +kernel
theorem fusedMap3704swap_checked : acceptsGraphIso
    (fused (graph core3704) (root 5) 8 0) DegreeTwoThreeSpectrum3882.graph fusedMap3704swap=true := by decide +kernel
theorem certified3704swap : Certified (graph core3704) (root 5) 8 0 :=
  of_native_maps core3704 DegreeTwoThreeSpectrum3878.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap3704swap fusedMap3704swap sourceMap3704swap_checked fusedMap3704swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3704
#print axioms sourceMap3704swap_checked
#print axioms fusedMap3704swap_checked
#print axioms certified3704swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
