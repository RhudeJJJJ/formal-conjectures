/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3570 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap3570 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3570 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3570_checked : acceptsGraphIso
    (source (graph core3570) (root 8) 0 6) DegreeTwoThreeSpectrum5256.graph sourceMap3570=true := by decide +kernel
theorem fusedMap3570_checked : acceptsGraphIso
    (fused (graph core3570) (root 8) 0 6) DegreeTwoThreeSpectrum5258.graph fusedMap3570=true := by decide +kernel
theorem certified3570 : Certified (graph core3570) (root 8) 0 6 :=
  of_native_maps core3570 DegreeTwoThreeSpectrum5256.graph DegreeTwoThreeSpectrum5258.graph
    sourceMap3570 fusedMap3570 sourceMap3570_checked fusedMap3570_checked
    DegreeTwoThreeFiniteComparisons.comparison3570
#print axioms sourceMap3570_checked
#print axioms fusedMap3570_checked
#print axioms certified3570
def sourceMap3570swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3570swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3570swap_checked : acceptsGraphIso
    (source (graph core3570) (root 8) 6 0) DegreeTwoThreeSpectrum5256.graph sourceMap3570swap=true := by decide +kernel
theorem fusedMap3570swap_checked : acceptsGraphIso
    (fused (graph core3570) (root 8) 6 0) DegreeTwoThreeSpectrum5258.graph fusedMap3570swap=true := by decide +kernel
theorem certified3570swap : Certified (graph core3570) (root 8) 6 0 :=
  of_native_maps core3570 DegreeTwoThreeSpectrum5256.graph DegreeTwoThreeSpectrum5258.graph
    sourceMap3570swap fusedMap3570swap sourceMap3570swap_checked fusedMap3570swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3570
#print axioms sourceMap3570swap_checked
#print axioms fusedMap3570swap_checked
#print axioms certified3570swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
