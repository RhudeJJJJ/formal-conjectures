/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1978 : Family 10 := level10.get ⟨299,by decide⟩
def sourceMap1978 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1978 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1978_checked : acceptsGraphIso
    (source (graph core1978) (root 10) 0 0) DegreeOneSmallSpectrum1105.graph sourceMap1978=true := by decide +kernel
theorem fusedMap1978_checked : acceptsGraphIso
    (fused (graph core1978) (root 10) 0 0) DegreeOneSmallSpectrum1343.graph fusedMap1978=true := by decide +kernel
theorem certified1978 : Certified (graph core1978) (root 10) 0 0 :=
  of_native_maps core1978 DegreeOneSmallSpectrum1105.graph DegreeOneSmallSpectrum1343.graph
    sourceMap1978 fusedMap1978 sourceMap1978_checked fusedMap1978_checked
    DegreeOneSmallComparisons.comparison1978
#print axioms sourceMap1978_checked
#print axioms fusedMap1978_checked
#print axioms certified1978
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
