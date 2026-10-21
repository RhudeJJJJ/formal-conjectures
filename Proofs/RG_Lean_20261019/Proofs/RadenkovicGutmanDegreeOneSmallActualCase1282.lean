/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1282 : Family 9 := level9.get ⟨53,by decide⟩
def sourceMap1282 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1282 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1282_checked : acceptsGraphIso
    (source (graph core1282) (root 9) 0 1) DegreeOneSmallSpectrum1172.graph sourceMap1282=true := by decide +kernel
theorem fusedMap1282_checked : acceptsGraphIso
    (fused (graph core1282) (root 9) 0 1) DegreeOneSmallSpectrum878.graph fusedMap1282=true := by decide +kernel
theorem certified1282 : Certified (graph core1282) (root 9) 0 1 :=
  of_native_maps core1282 DegreeOneSmallSpectrum1172.graph DegreeOneSmallSpectrum878.graph
    sourceMap1282 fusedMap1282 sourceMap1282_checked fusedMap1282_checked
    DegreeOneSmallComparisons.comparison1282
#print axioms sourceMap1282_checked
#print axioms fusedMap1282_checked
#print axioms certified1282
def sourceMap1282swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1282swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1282swap_checked : acceptsGraphIso
    (source (graph core1282) (root 9) 1 0) DegreeOneSmallSpectrum1172.graph sourceMap1282swap=true := by decide +kernel
theorem fusedMap1282swap_checked : acceptsGraphIso
    (fused (graph core1282) (root 9) 1 0) DegreeOneSmallSpectrum878.graph fusedMap1282swap=true := by decide +kernel
theorem certified1282swap : Certified (graph core1282) (root 9) 1 0 :=
  of_native_maps core1282 DegreeOneSmallSpectrum1172.graph DegreeOneSmallSpectrum878.graph
    sourceMap1282swap fusedMap1282swap sourceMap1282swap_checked fusedMap1282swap_checked
    DegreeOneSmallComparisons.comparison1282
#print axioms sourceMap1282swap_checked
#print axioms fusedMap1282swap_checked
#print axioms certified1282swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
