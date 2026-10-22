/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1855 : Family 10 := level10.get ⟨1266,by decide⟩
def sourceMap1855 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1855 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1855_checked : acceptsGraphIso
    (source (graph core1855) (root 10) 0 2) DegreeTwoThreeSpectrum3413.graph sourceMap1855=true := by decide +kernel
theorem fusedMap1855_checked : acceptsGraphIso
    (fused (graph core1855) (root 10) 0 2) DegreeTwoThreeSpectrum3417.graph fusedMap1855=true := by decide +kernel
theorem certified1855 : Certified (graph core1855) (root 10) 0 2 :=
  of_native_maps core1855 DegreeTwoThreeSpectrum3413.graph DegreeTwoThreeSpectrum3417.graph
    sourceMap1855 fusedMap1855 sourceMap1855_checked fusedMap1855_checked
    DegreeTwoThreeFiniteComparisons.comparison1855
#print axioms sourceMap1855_checked
#print axioms fusedMap1855_checked
#print axioms certified1855
def sourceMap1855swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1855swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1855swap_checked : acceptsGraphIso
    (source (graph core1855) (root 10) 2 0) DegreeTwoThreeSpectrum3413.graph sourceMap1855swap=true := by decide +kernel
theorem fusedMap1855swap_checked : acceptsGraphIso
    (fused (graph core1855) (root 10) 2 0) DegreeTwoThreeSpectrum3417.graph fusedMap1855swap=true := by decide +kernel
theorem certified1855swap : Certified (graph core1855) (root 10) 2 0 :=
  of_native_maps core1855 DegreeTwoThreeSpectrum3413.graph DegreeTwoThreeSpectrum3417.graph
    sourceMap1855swap fusedMap1855swap sourceMap1855swap_checked fusedMap1855swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1855
#print axioms sourceMap1855swap_checked
#print axioms fusedMap1855swap_checked
#print axioms certified1855swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
