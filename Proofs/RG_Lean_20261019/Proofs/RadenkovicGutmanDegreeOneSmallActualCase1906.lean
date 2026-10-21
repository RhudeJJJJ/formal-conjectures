/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1906 : Family 10 := level10.get ⟨191,by decide⟩
def sourceMap1906 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1906 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1906_checked : acceptsGraphIso
    (source (graph core1906) (root 10) 0 0) DegreeOneSmallSpectrum995.graph sourceMap1906=true := by decide +kernel
theorem fusedMap1906_checked : acceptsGraphIso
    (fused (graph core1906) (root 10) 0 0) DegreeOneSmallSpectrum998.graph fusedMap1906=true := by decide +kernel
theorem certified1906 : Certified (graph core1906) (root 10) 0 0 :=
  of_native_maps core1906 DegreeOneSmallSpectrum995.graph DegreeOneSmallSpectrum998.graph
    sourceMap1906 fusedMap1906 sourceMap1906_checked fusedMap1906_checked
    DegreeOneSmallComparisons.comparison1906
#print axioms sourceMap1906_checked
#print axioms fusedMap1906_checked
#print axioms certified1906
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
