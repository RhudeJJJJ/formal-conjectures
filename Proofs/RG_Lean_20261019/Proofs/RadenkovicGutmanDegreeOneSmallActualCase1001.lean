/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1001 : Family 8 := level8.get ⟨100,by decide⟩
def sourceMap1001 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1001 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1001_checked : acceptsGraphIso
    (source (graph core1001) (root 8) 0 2) DegreeOneSmallSpectrum1020.graph sourceMap1001=true := by decide +kernel
theorem fusedMap1001_checked : acceptsGraphIso
    (fused (graph core1001) (root 8) 0 2) DegreeOneSmallSpectrum1021.graph fusedMap1001=true := by decide +kernel
theorem certified1001 : Certified (graph core1001) (root 8) 0 2 :=
  of_native_maps core1001 DegreeOneSmallSpectrum1020.graph DegreeOneSmallSpectrum1021.graph
    sourceMap1001 fusedMap1001 sourceMap1001_checked fusedMap1001_checked
    DegreeOneSmallComparisons.comparison1001
#print axioms sourceMap1001_checked
#print axioms fusedMap1001_checked
#print axioms certified1001
def sourceMap1001swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1001swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1001swap_checked : acceptsGraphIso
    (source (graph core1001) (root 8) 2 0) DegreeOneSmallSpectrum1020.graph sourceMap1001swap=true := by decide +kernel
theorem fusedMap1001swap_checked : acceptsGraphIso
    (fused (graph core1001) (root 8) 2 0) DegreeOneSmallSpectrum1021.graph fusedMap1001swap=true := by decide +kernel
theorem certified1001swap : Certified (graph core1001) (root 8) 2 0 :=
  of_native_maps core1001 DegreeOneSmallSpectrum1020.graph DegreeOneSmallSpectrum1021.graph
    sourceMap1001swap fusedMap1001swap sourceMap1001swap_checked fusedMap1001swap_checked
    DegreeOneSmallComparisons.comparison1001
#print axioms sourceMap1001swap_checked
#print axioms fusedMap1001swap_checked
#print axioms certified1001swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
