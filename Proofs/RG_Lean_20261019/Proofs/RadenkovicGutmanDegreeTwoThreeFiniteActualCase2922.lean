/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2922 : Family 10 := level10.get ⟨1371,by decide⟩
def sourceMap2922 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2922 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2922_checked : acceptsGraphIso
    (source (graph core2922) (root 10) 0 4) DegreeTwoThreeSpectrum6713.graph sourceMap2922=true := by decide +kernel
theorem fusedMap2922_checked : acceptsGraphIso
    (fused (graph core2922) (root 10) 0 4) DegreeTwoThreeSpectrum6714.graph fusedMap2922=true := by decide +kernel
theorem certified2922 : Certified (graph core2922) (root 10) 0 4 :=
  of_native_maps core2922 DegreeTwoThreeSpectrum6713.graph DegreeTwoThreeSpectrum6714.graph
    sourceMap2922 fusedMap2922 sourceMap2922_checked fusedMap2922_checked
    DegreeTwoThreeFiniteComparisons.comparison2922
#print axioms sourceMap2922_checked
#print axioms fusedMap2922_checked
#print axioms certified2922
def sourceMap2922swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2922swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2922swap_checked : acceptsGraphIso
    (source (graph core2922) (root 10) 4 0) DegreeTwoThreeSpectrum6713.graph sourceMap2922swap=true := by decide +kernel
theorem fusedMap2922swap_checked : acceptsGraphIso
    (fused (graph core2922) (root 10) 4 0) DegreeTwoThreeSpectrum6714.graph fusedMap2922swap=true := by decide +kernel
theorem certified2922swap : Certified (graph core2922) (root 10) 4 0 :=
  of_native_maps core2922 DegreeTwoThreeSpectrum6713.graph DegreeTwoThreeSpectrum6714.graph
    sourceMap2922swap fusedMap2922swap sourceMap2922swap_checked fusedMap2922swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2922
#print axioms sourceMap2922swap_checked
#print axioms fusedMap2922swap_checked
#print axioms certified2922swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
