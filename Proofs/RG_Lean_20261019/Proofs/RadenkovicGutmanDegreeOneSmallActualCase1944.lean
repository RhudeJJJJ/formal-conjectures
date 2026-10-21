/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1944 : Family 10 := level10.get ⟨243,by decide⟩
def sourceMap1944 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1944 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1944_checked : acceptsGraphIso
    (source (graph core1944) (root 10) 0 0) DegreeOneSmallSpectrum1202.graph sourceMap1944=true := by decide +kernel
theorem fusedMap1944_checked : acceptsGraphIso
    (fused (graph core1944) (root 10) 0 0) DegreeOneSmallSpectrum1211.graph fusedMap1944=true := by decide +kernel
theorem certified1944 : Certified (graph core1944) (root 10) 0 0 :=
  of_native_maps core1944 DegreeOneSmallSpectrum1202.graph DegreeOneSmallSpectrum1211.graph
    sourceMap1944 fusedMap1944 sourceMap1944_checked fusedMap1944_checked
    DegreeOneSmallComparisons.comparison1944
#print axioms sourceMap1944_checked
#print axioms fusedMap1944_checked
#print axioms certified1944
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
