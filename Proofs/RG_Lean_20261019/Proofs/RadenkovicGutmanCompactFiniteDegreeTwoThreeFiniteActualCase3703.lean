/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3703 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3703 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (sourceLabel 4 0 8 v)
def fusedMap3703 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 0 8 v)
theorem sourceMap3703_checked : acceptsGraphIso
    (source (graph core3703) (root 4) 0 8) DegreeTwoThreeSpectrum2349.graph sourceMap3703=true := by decide +kernel
theorem fusedMap3703_checked : acceptsGraphIso
    (fused (graph core3703) (root 4) 0 8) DegreeTwoThreeSpectrum2354.graph fusedMap3703=true := by decide +kernel
theorem certified3703 : Certified (graph core3703) (root 4) 0 8 :=
  of_native_maps core3703 DegreeTwoThreeSpectrum2349.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap3703 fusedMap3703 sourceMap3703_checked fusedMap3703_checked
    DegreeTwoThreeFiniteComparisons.comparison3703
#print axioms sourceMap3703_checked
#print axioms fusedMap3703_checked
#print axioms certified3703
def sourceMap3703swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,14,8] (sourceLabel 4 8 0 v)
def fusedMap3703swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 8 0 v)
theorem sourceMap3703swap_checked : acceptsGraphIso
    (source (graph core3703) (root 4) 8 0) DegreeTwoThreeSpectrum2349.graph sourceMap3703swap=true := by decide +kernel
theorem fusedMap3703swap_checked : acceptsGraphIso
    (fused (graph core3703) (root 4) 8 0) DegreeTwoThreeSpectrum2354.graph fusedMap3703swap=true := by decide +kernel
theorem certified3703swap : Certified (graph core3703) (root 4) 8 0 :=
  of_native_maps core3703 DegreeTwoThreeSpectrum2349.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap3703swap fusedMap3703swap sourceMap3703swap_checked fusedMap3703swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3703
#print axioms sourceMap3703swap_checked
#print axioms fusedMap3703swap_checked
#print axioms certified3703swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
