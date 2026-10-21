/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1919 : Family 10 := level10.get ⟨207,by decide⟩
def sourceMap1919 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1919 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1919_checked : acceptsGraphIso
    (source (graph core1919) (root 10) 0 0) DegreeOneSmallSpectrum1065.graph sourceMap1919=true := by decide +kernel
theorem fusedMap1919_checked : acceptsGraphIso
    (fused (graph core1919) (root 10) 0 0) DegreeOneSmallSpectrum1082.graph fusedMap1919=true := by decide +kernel
theorem certified1919 : Certified (graph core1919) (root 10) 0 0 :=
  of_native_maps core1919 DegreeOneSmallSpectrum1065.graph DegreeOneSmallSpectrum1082.graph
    sourceMap1919 fusedMap1919 sourceMap1919_checked fusedMap1919_checked
    DegreeOneSmallComparisons.comparison1919
#print axioms sourceMap1919_checked
#print axioms fusedMap1919_checked
#print axioms certified1919
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
