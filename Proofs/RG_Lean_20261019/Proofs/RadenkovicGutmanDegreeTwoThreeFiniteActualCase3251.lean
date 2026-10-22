/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3251 : Family 9 := level9.get ⟨78,by decide⟩
def sourceMap3251 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3251 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3251_checked : acceptsGraphIso
    (source (graph core3251) (root 9) 0 5) DegreeTwoThreeSpectrum5539.graph sourceMap3251=true := by decide +kernel
theorem fusedMap3251_checked : acceptsGraphIso
    (fused (graph core3251) (root 9) 0 5) DegreeTwoThreeSpectrum5018.graph fusedMap3251=true := by decide +kernel
theorem certified3251 : Certified (graph core3251) (root 9) 0 5 :=
  of_native_maps core3251 DegreeTwoThreeSpectrum5539.graph DegreeTwoThreeSpectrum5018.graph
    sourceMap3251 fusedMap3251 sourceMap3251_checked fusedMap3251_checked
    DegreeTwoThreeFiniteComparisons.comparison3251
#print axioms sourceMap3251_checked
#print axioms fusedMap3251_checked
#print axioms certified3251
def sourceMap3251swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3251swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3251swap_checked : acceptsGraphIso
    (source (graph core3251) (root 9) 5 0) DegreeTwoThreeSpectrum5539.graph sourceMap3251swap=true := by decide +kernel
theorem fusedMap3251swap_checked : acceptsGraphIso
    (fused (graph core3251) (root 9) 5 0) DegreeTwoThreeSpectrum5018.graph fusedMap3251swap=true := by decide +kernel
theorem certified3251swap : Certified (graph core3251) (root 9) 5 0 :=
  of_native_maps core3251 DegreeTwoThreeSpectrum5539.graph DegreeTwoThreeSpectrum5018.graph
    sourceMap3251swap fusedMap3251swap sourceMap3251swap_checked fusedMap3251swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3251
#print axioms sourceMap3251swap_checked
#print axioms fusedMap3251swap_checked
#print axioms certified3251swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
