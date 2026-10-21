/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1961 : Family 10 := level10.get ⟨268,by decide⟩
def sourceMap1961 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1961 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1961_checked : acceptsGraphIso
    (source (graph core1961) (root 10) 0 0) DegreeOneSmallSpectrum1121.graph sourceMap1961=true := by decide +kernel
theorem fusedMap1961_checked : acceptsGraphIso
    (fused (graph core1961) (root 10) 0 0) DegreeOneSmallSpectrum1285.graph fusedMap1961=true := by decide +kernel
theorem certified1961 : Certified (graph core1961) (root 10) 0 0 :=
  of_native_maps core1961 DegreeOneSmallSpectrum1121.graph DegreeOneSmallSpectrum1285.graph
    sourceMap1961 fusedMap1961 sourceMap1961_checked fusedMap1961_checked
    DegreeOneSmallComparisons.comparison1961
#print axioms sourceMap1961_checked
#print axioms fusedMap1961_checked
#print axioms certified1961
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
