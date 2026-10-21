/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1290 : Family 9 := level9.get ⟨58,by decide⟩
def sourceMap1290 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1290 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1290_checked : acceptsGraphIso
    (source (graph core1290) (root 9) 0 1) DegreeOneSmallSpectrum1237.graph sourceMap1290=true := by decide +kernel
theorem fusedMap1290_checked : acceptsGraphIso
    (fused (graph core1290) (root 9) 0 1) DegreeOneSmallSpectrum886.graph fusedMap1290=true := by decide +kernel
theorem certified1290 : Certified (graph core1290) (root 9) 0 1 :=
  of_native_maps core1290 DegreeOneSmallSpectrum1237.graph DegreeOneSmallSpectrum886.graph
    sourceMap1290 fusedMap1290 sourceMap1290_checked fusedMap1290_checked
    DegreeOneSmallComparisons.comparison1290
#print axioms sourceMap1290_checked
#print axioms fusedMap1290_checked
#print axioms certified1290
def sourceMap1290swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1290swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1290swap_checked : acceptsGraphIso
    (source (graph core1290) (root 9) 1 0) DegreeOneSmallSpectrum1237.graph sourceMap1290swap=true := by decide +kernel
theorem fusedMap1290swap_checked : acceptsGraphIso
    (fused (graph core1290) (root 9) 1 0) DegreeOneSmallSpectrum886.graph fusedMap1290swap=true := by decide +kernel
theorem certified1290swap : Certified (graph core1290) (root 9) 1 0 :=
  of_native_maps core1290 DegreeOneSmallSpectrum1237.graph DegreeOneSmallSpectrum886.graph
    sourceMap1290swap fusedMap1290swap sourceMap1290swap_checked fusedMap1290swap_checked
    DegreeOneSmallComparisons.comparison1290
#print axioms sourceMap1290swap_checked
#print axioms fusedMap1290swap_checked
#print axioms certified1290swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
