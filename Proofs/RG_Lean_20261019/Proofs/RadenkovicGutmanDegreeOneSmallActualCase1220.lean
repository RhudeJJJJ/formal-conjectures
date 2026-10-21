/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1220 : Family 9 := level9.get ⟨13,by decide⟩
def sourceMap1220 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1220 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1220_checked : acceptsGraphIso
    (source (graph core1220) (root 9) 0 1) DegreeOneSmallSpectrum899.graph sourceMap1220=true := by decide +kernel
theorem fusedMap1220_checked : acceptsGraphIso
    (fused (graph core1220) (root 9) 0 1) DegreeOneSmallSpectrum908.graph fusedMap1220=true := by decide +kernel
theorem certified1220 : Certified (graph core1220) (root 9) 0 1 :=
  of_native_maps core1220 DegreeOneSmallSpectrum899.graph DegreeOneSmallSpectrum908.graph
    sourceMap1220 fusedMap1220 sourceMap1220_checked fusedMap1220_checked
    DegreeOneSmallComparisons.comparison1220
#print axioms sourceMap1220_checked
#print axioms fusedMap1220_checked
#print axioms certified1220
def sourceMap1220swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1220swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1220swap_checked : acceptsGraphIso
    (source (graph core1220) (root 9) 1 0) DegreeOneSmallSpectrum899.graph sourceMap1220swap=true := by decide +kernel
theorem fusedMap1220swap_checked : acceptsGraphIso
    (fused (graph core1220) (root 9) 1 0) DegreeOneSmallSpectrum908.graph fusedMap1220swap=true := by decide +kernel
theorem certified1220swap : Certified (graph core1220) (root 9) 1 0 :=
  of_native_maps core1220 DegreeOneSmallSpectrum899.graph DegreeOneSmallSpectrum908.graph
    sourceMap1220swap fusedMap1220swap sourceMap1220swap_checked fusedMap1220swap_checked
    DegreeOneSmallComparisons.comparison1220
#print axioms sourceMap1220swap_checked
#print axioms fusedMap1220swap_checked
#print axioms certified1220swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
