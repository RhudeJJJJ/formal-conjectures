/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1344 : Family 9 := level9.get ⟨97,by decide⟩
def sourceMap1344 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1344 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1344_checked : acceptsGraphIso
    (source (graph core1344) (root 9) 0 1) DegreeOneSmallSpectrum1430.graph sourceMap1344=true := by decide +kernel
theorem fusedMap1344_checked : acceptsGraphIso
    (fused (graph core1344) (root 9) 0 1) DegreeOneSmallSpectrum950.graph fusedMap1344=true := by decide +kernel
theorem certified1344 : Certified (graph core1344) (root 9) 0 1 :=
  of_native_maps core1344 DegreeOneSmallSpectrum1430.graph DegreeOneSmallSpectrum950.graph
    sourceMap1344 fusedMap1344 sourceMap1344_checked fusedMap1344_checked
    DegreeOneSmallComparisons.comparison1344
#print axioms sourceMap1344_checked
#print axioms fusedMap1344_checked
#print axioms certified1344
def sourceMap1344swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1344swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1344swap_checked : acceptsGraphIso
    (source (graph core1344) (root 9) 1 0) DegreeOneSmallSpectrum1430.graph sourceMap1344swap=true := by decide +kernel
theorem fusedMap1344swap_checked : acceptsGraphIso
    (fused (graph core1344) (root 9) 1 0) DegreeOneSmallSpectrum950.graph fusedMap1344swap=true := by decide +kernel
theorem certified1344swap : Certified (graph core1344) (root 9) 1 0 :=
  of_native_maps core1344 DegreeOneSmallSpectrum1430.graph DegreeOneSmallSpectrum950.graph
    sourceMap1344swap fusedMap1344swap sourceMap1344swap_checked fusedMap1344swap_checked
    DegreeOneSmallComparisons.comparison1344
#print axioms sourceMap1344swap_checked
#print axioms fusedMap1344swap_checked
#print axioms certified1344swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
