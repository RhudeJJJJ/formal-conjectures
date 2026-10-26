/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3800 : Family 7 := level7.get ⟨41,by decide⟩
def sourceMap3800 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3800 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3800_checked : acceptsGraphIso
    (source (graph core3800) (root 7) 1 4) DegreeTwoThreeSpectrum2674.graph sourceMap3800=true := by decide +kernel
theorem fusedMap3800_checked : acceptsGraphIso
    (fused (graph core3800) (root 7) 1 4) DegreeTwoThreeSpectrum2351.graph fusedMap3800=true := by decide +kernel
theorem certified3800 : Certified (graph core3800) (root 7) 1 4 :=
  of_native_maps core3800 DegreeTwoThreeSpectrum2674.graph DegreeTwoThreeSpectrum2351.graph
    sourceMap3800 fusedMap3800 sourceMap3800_checked fusedMap3800_checked
    DegreeTwoThreeFiniteComparisons.comparison3800
#print axioms sourceMap3800_checked
#print axioms fusedMap3800_checked
#print axioms certified3800
def sourceMap3800swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3800swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3800swap_checked : acceptsGraphIso
    (source (graph core3800) (root 7) 4 1) DegreeTwoThreeSpectrum2674.graph sourceMap3800swap=true := by decide +kernel
theorem fusedMap3800swap_checked : acceptsGraphIso
    (fused (graph core3800) (root 7) 4 1) DegreeTwoThreeSpectrum2351.graph fusedMap3800swap=true := by decide +kernel
theorem certified3800swap : Certified (graph core3800) (root 7) 4 1 :=
  of_native_maps core3800 DegreeTwoThreeSpectrum2674.graph DegreeTwoThreeSpectrum2351.graph
    sourceMap3800swap fusedMap3800swap sourceMap3800swap_checked fusedMap3800swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3800
#print axioms sourceMap3800swap_checked
#print axioms fusedMap3800swap_checked
#print axioms certified3800swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
