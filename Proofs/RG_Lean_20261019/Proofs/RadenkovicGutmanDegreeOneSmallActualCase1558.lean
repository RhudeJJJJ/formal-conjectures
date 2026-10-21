/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1558 : Family 9 := level9.get ⟨289,by decide⟩
def sourceMap1558 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1558 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1558_checked : acceptsGraphIso
    (source (graph core1558) (root 9) 0 1) DegreeOneSmallSpectrum1394.graph sourceMap1558=true := by decide +kernel
theorem fusedMap1558_checked : acceptsGraphIso
    (fused (graph core1558) (root 9) 0 1) DegreeOneSmallSpectrum1510.graph fusedMap1558=true := by decide +kernel
theorem certified1558 : Certified (graph core1558) (root 9) 0 1 :=
  of_native_maps core1558 DegreeOneSmallSpectrum1394.graph DegreeOneSmallSpectrum1510.graph
    sourceMap1558 fusedMap1558 sourceMap1558_checked fusedMap1558_checked
    DegreeOneSmallComparisons.comparison1558
#print axioms sourceMap1558_checked
#print axioms fusedMap1558_checked
#print axioms certified1558
def sourceMap1558swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1558swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1558swap_checked : acceptsGraphIso
    (source (graph core1558) (root 9) 1 0) DegreeOneSmallSpectrum1394.graph sourceMap1558swap=true := by decide +kernel
theorem fusedMap1558swap_checked : acceptsGraphIso
    (fused (graph core1558) (root 9) 1 0) DegreeOneSmallSpectrum1510.graph fusedMap1558swap=true := by decide +kernel
theorem certified1558swap : Certified (graph core1558) (root 9) 1 0 :=
  of_native_maps core1558 DegreeOneSmallSpectrum1394.graph DegreeOneSmallSpectrum1510.graph
    sourceMap1558swap fusedMap1558swap sourceMap1558swap_checked fusedMap1558swap_checked
    DegreeOneSmallComparisons.comparison1558
#print axioms sourceMap1558swap_checked
#print axioms fusedMap1558swap_checked
#print axioms certified1558swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
