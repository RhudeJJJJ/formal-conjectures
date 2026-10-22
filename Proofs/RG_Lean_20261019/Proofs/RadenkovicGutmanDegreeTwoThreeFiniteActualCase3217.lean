/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3217 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap3217 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3217 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3217_checked : acceptsGraphIso
    (source (graph core3217) (root 8) 0 5) DegreeTwoThreeSpectrum4329.graph sourceMap3217=true := by decide +kernel
theorem fusedMap3217_checked : acceptsGraphIso
    (fused (graph core3217) (root 8) 0 5) DegreeTwoThreeSpectrum4330.graph fusedMap3217=true := by decide +kernel
theorem certified3217 : Certified (graph core3217) (root 8) 0 5 :=
  of_native_maps core3217 DegreeTwoThreeSpectrum4329.graph DegreeTwoThreeSpectrum4330.graph
    sourceMap3217 fusedMap3217 sourceMap3217_checked fusedMap3217_checked
    DegreeTwoThreeFiniteComparisons.comparison3217
#print axioms sourceMap3217_checked
#print axioms fusedMap3217_checked
#print axioms certified3217
def sourceMap3217swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3217swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3217swap_checked : acceptsGraphIso
    (source (graph core3217) (root 8) 5 0) DegreeTwoThreeSpectrum4329.graph sourceMap3217swap=true := by decide +kernel
theorem fusedMap3217swap_checked : acceptsGraphIso
    (fused (graph core3217) (root 8) 5 0) DegreeTwoThreeSpectrum4330.graph fusedMap3217swap=true := by decide +kernel
theorem certified3217swap : Certified (graph core3217) (root 8) 5 0 :=
  of_native_maps core3217 DegreeTwoThreeSpectrum4329.graph DegreeTwoThreeSpectrum4330.graph
    sourceMap3217swap fusedMap3217swap sourceMap3217swap_checked fusedMap3217swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3217
#print axioms sourceMap3217swap_checked
#print axioms fusedMap3217swap_checked
#print axioms certified3217swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
