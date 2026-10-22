/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3043 : Family 10 := level10.get ⟨1669,by decide⟩
def sourceMap3043 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3043 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3043_checked : acceptsGraphIso
    (source (graph core3043) (root 10) 0 4) DegreeTwoThreeSpectrum7237.graph sourceMap3043=true := by decide +kernel
theorem fusedMap3043_checked : acceptsGraphIso
    (fused (graph core3043) (root 10) 0 4) DegreeTwoThreeSpectrum6289.graph fusedMap3043=true := by decide +kernel
theorem certified3043 : Certified (graph core3043) (root 10) 0 4 :=
  of_native_maps core3043 DegreeTwoThreeSpectrum7237.graph DegreeTwoThreeSpectrum6289.graph
    sourceMap3043 fusedMap3043 sourceMap3043_checked fusedMap3043_checked
    DegreeTwoThreeFiniteComparisons.comparison3043
#print axioms sourceMap3043_checked
#print axioms fusedMap3043_checked
#print axioms certified3043
def sourceMap3043swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3043swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3043swap_checked : acceptsGraphIso
    (source (graph core3043) (root 10) 4 0) DegreeTwoThreeSpectrum7237.graph sourceMap3043swap=true := by decide +kernel
theorem fusedMap3043swap_checked : acceptsGraphIso
    (fused (graph core3043) (root 10) 4 0) DegreeTwoThreeSpectrum6289.graph fusedMap3043swap=true := by decide +kernel
theorem certified3043swap : Certified (graph core3043) (root 10) 4 0 :=
  of_native_maps core3043 DegreeTwoThreeSpectrum7237.graph DegreeTwoThreeSpectrum6289.graph
    sourceMap3043swap fusedMap3043swap sourceMap3043swap_checked fusedMap3043swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3043
#print axioms sourceMap3043swap_checked
#print axioms fusedMap3043swap_checked
#print axioms certified3043swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
