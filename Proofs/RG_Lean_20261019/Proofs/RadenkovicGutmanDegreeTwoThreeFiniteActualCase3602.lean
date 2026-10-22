/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3602 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap3602 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3602 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3602_checked : acceptsGraphIso
    (source (graph core3602) (root 8) 0 6) DegreeTwoThreeSpectrum6014.graph sourceMap3602=true := by decide +kernel
theorem fusedMap3602_checked : acceptsGraphIso
    (fused (graph core3602) (root 8) 0 6) DegreeTwoThreeSpectrum5141.graph fusedMap3602=true := by decide +kernel
theorem certified3602 : Certified (graph core3602) (root 8) 0 6 :=
  of_native_maps core3602 DegreeTwoThreeSpectrum6014.graph DegreeTwoThreeSpectrum5141.graph
    sourceMap3602 fusedMap3602 sourceMap3602_checked fusedMap3602_checked
    DegreeTwoThreeFiniteComparisons.comparison3602
#print axioms sourceMap3602_checked
#print axioms fusedMap3602_checked
#print axioms certified3602
def sourceMap3602swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3602swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3602swap_checked : acceptsGraphIso
    (source (graph core3602) (root 8) 6 0) DegreeTwoThreeSpectrum6014.graph sourceMap3602swap=true := by decide +kernel
theorem fusedMap3602swap_checked : acceptsGraphIso
    (fused (graph core3602) (root 8) 6 0) DegreeTwoThreeSpectrum5141.graph fusedMap3602swap=true := by decide +kernel
theorem certified3602swap : Certified (graph core3602) (root 8) 6 0 :=
  of_native_maps core3602 DegreeTwoThreeSpectrum6014.graph DegreeTwoThreeSpectrum5141.graph
    sourceMap3602swap fusedMap3602swap sourceMap3602swap_checked fusedMap3602swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3602
#print axioms sourceMap3602swap_checked
#print axioms fusedMap3602swap_checked
#print axioms certified3602swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
