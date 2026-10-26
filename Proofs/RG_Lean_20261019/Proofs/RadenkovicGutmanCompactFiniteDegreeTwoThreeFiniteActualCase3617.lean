/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3617 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap3617 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3617 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3617_checked : acceptsGraphIso
    (source (graph core3617) (root 8) 0 6) DegreeTwoThreeSpectrum6344.graph sourceMap3617=true := by decide +kernel
theorem fusedMap3617_checked : acceptsGraphIso
    (fused (graph core3617) (root 8) 0 6) DegreeTwoThreeSpectrum5306.graph fusedMap3617=true := by decide +kernel
theorem certified3617 : Certified (graph core3617) (root 8) 0 6 :=
  of_native_maps core3617 DegreeTwoThreeSpectrum6344.graph DegreeTwoThreeSpectrum5306.graph
    sourceMap3617 fusedMap3617 sourceMap3617_checked fusedMap3617_checked
    DegreeTwoThreeFiniteComparisons.comparison3617
#print axioms sourceMap3617_checked
#print axioms fusedMap3617_checked
#print axioms certified3617
def sourceMap3617swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3617swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3617swap_checked : acceptsGraphIso
    (source (graph core3617) (root 8) 6 0) DegreeTwoThreeSpectrum6344.graph sourceMap3617swap=true := by decide +kernel
theorem fusedMap3617swap_checked : acceptsGraphIso
    (fused (graph core3617) (root 8) 6 0) DegreeTwoThreeSpectrum5306.graph fusedMap3617swap=true := by decide +kernel
theorem certified3617swap : Certified (graph core3617) (root 8) 6 0 :=
  of_native_maps core3617 DegreeTwoThreeSpectrum6344.graph DegreeTwoThreeSpectrum5306.graph
    sourceMap3617swap fusedMap3617swap sourceMap3617swap_checked fusedMap3617swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3617
#print axioms sourceMap3617swap_checked
#print axioms fusedMap3617swap_checked
#print axioms certified3617swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
