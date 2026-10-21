/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1017 : Family 8 := level8.get ⟨108,by decide⟩
def sourceMap1017 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1017 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1017_checked : acceptsGraphIso
    (source (graph core1017) (root 8) 0 2) DegreeOneSmallSpectrum1087.graph sourceMap1017=true := by decide +kernel
theorem fusedMap1017_checked : acceptsGraphIso
    (fused (graph core1017) (root 8) 0 2) DegreeOneSmallSpectrum1088.graph fusedMap1017=true := by decide +kernel
theorem certified1017 : Certified (graph core1017) (root 8) 0 2 :=
  of_native_maps core1017 DegreeOneSmallSpectrum1087.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1017 fusedMap1017 sourceMap1017_checked fusedMap1017_checked
    DegreeOneSmallComparisons.comparison1017
#print axioms sourceMap1017_checked
#print axioms fusedMap1017_checked
#print axioms certified1017
def sourceMap1017swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1017swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1017swap_checked : acceptsGraphIso
    (source (graph core1017) (root 8) 2 0) DegreeOneSmallSpectrum1087.graph sourceMap1017swap=true := by decide +kernel
theorem fusedMap1017swap_checked : acceptsGraphIso
    (fused (graph core1017) (root 8) 2 0) DegreeOneSmallSpectrum1088.graph fusedMap1017swap=true := by decide +kernel
theorem certified1017swap : Certified (graph core1017) (root 8) 2 0 :=
  of_native_maps core1017 DegreeOneSmallSpectrum1087.graph DegreeOneSmallSpectrum1088.graph
    sourceMap1017swap fusedMap1017swap sourceMap1017swap_checked fusedMap1017swap_checked
    DegreeOneSmallComparisons.comparison1017
#print axioms sourceMap1017swap_checked
#print axioms fusedMap1017swap_checked
#print axioms certified1017swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
