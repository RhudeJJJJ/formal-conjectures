/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1232 : Family 9 := level9.get ⟨20,by decide⟩
def sourceMap1232 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1232 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1232_checked : acceptsGraphIso
    (source (graph core1232) (root 9) 0 1) DegreeOneSmallSpectrum932.graph sourceMap1232=true := by decide +kernel
theorem fusedMap1232_checked : acceptsGraphIso
    (fused (graph core1232) (root 9) 0 1) DegreeOneSmallSpectrum944.graph fusedMap1232=true := by decide +kernel
theorem certified1232 : Certified (graph core1232) (root 9) 0 1 :=
  of_native_maps core1232 DegreeOneSmallSpectrum932.graph DegreeOneSmallSpectrum944.graph
    sourceMap1232 fusedMap1232 sourceMap1232_checked fusedMap1232_checked
    DegreeOneSmallComparisons.comparison1232
#print axioms sourceMap1232_checked
#print axioms fusedMap1232_checked
#print axioms certified1232
def sourceMap1232swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1232swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1232swap_checked : acceptsGraphIso
    (source (graph core1232) (root 9) 1 0) DegreeOneSmallSpectrum932.graph sourceMap1232swap=true := by decide +kernel
theorem fusedMap1232swap_checked : acceptsGraphIso
    (fused (graph core1232) (root 9) 1 0) DegreeOneSmallSpectrum944.graph fusedMap1232swap=true := by decide +kernel
theorem certified1232swap : Certified (graph core1232) (root 9) 1 0 :=
  of_native_maps core1232 DegreeOneSmallSpectrum932.graph DegreeOneSmallSpectrum944.graph
    sourceMap1232swap fusedMap1232swap sourceMap1232swap_checked fusedMap1232swap_checked
    DegreeOneSmallComparisons.comparison1232
#print axioms sourceMap1232swap_checked
#print axioms fusedMap1232swap_checked
#print axioms certified1232swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
