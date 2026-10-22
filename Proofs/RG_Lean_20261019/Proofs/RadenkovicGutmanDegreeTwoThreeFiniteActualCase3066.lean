/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3066 : Family 10 := level10.get ⟨1746,by decide⟩
def sourceMap3066 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3066 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3066_checked : acceptsGraphIso
    (source (graph core3066) (root 10) 0 4) DegreeTwoThreeSpectrum7389.graph sourceMap3066=true := by decide +kernel
theorem fusedMap3066_checked : acceptsGraphIso
    (fused (graph core3066) (root 10) 0 4) DegreeTwoThreeSpectrum6600.graph fusedMap3066=true := by decide +kernel
theorem certified3066 : Certified (graph core3066) (root 10) 0 4 :=
  of_native_maps core3066 DegreeTwoThreeSpectrum7389.graph DegreeTwoThreeSpectrum6600.graph
    sourceMap3066 fusedMap3066 sourceMap3066_checked fusedMap3066_checked
    DegreeTwoThreeFiniteComparisons.comparison3066
#print axioms sourceMap3066_checked
#print axioms fusedMap3066_checked
#print axioms certified3066
def sourceMap3066swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3066swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3066swap_checked : acceptsGraphIso
    (source (graph core3066) (root 10) 4 0) DegreeTwoThreeSpectrum7389.graph sourceMap3066swap=true := by decide +kernel
theorem fusedMap3066swap_checked : acceptsGraphIso
    (fused (graph core3066) (root 10) 4 0) DegreeTwoThreeSpectrum6600.graph fusedMap3066swap=true := by decide +kernel
theorem certified3066swap : Certified (graph core3066) (root 10) 4 0 :=
  of_native_maps core3066 DegreeTwoThreeSpectrum7389.graph DegreeTwoThreeSpectrum6600.graph
    sourceMap3066swap fusedMap3066swap sourceMap3066swap_checked fusedMap3066swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3066
#print axioms sourceMap3066swap_checked
#print axioms fusedMap3066swap_checked
#print axioms certified3066swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
