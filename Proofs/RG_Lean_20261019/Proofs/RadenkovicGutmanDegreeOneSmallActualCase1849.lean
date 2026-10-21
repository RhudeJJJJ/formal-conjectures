/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1849 : Family 10 := level10.get ⟨102,by decide⟩
def sourceMap1849 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1849 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1849_checked : acceptsGraphIso
    (source (graph core1849) (root 10) 0 0) DegreeOneSmallSpectrum1237.graph sourceMap1849=true := by decide +kernel
theorem fusedMap1849_checked : acceptsGraphIso
    (fused (graph core1849) (root 10) 0 0) DegreeOneSmallSpectrum928.graph fusedMap1849=true := by decide +kernel
theorem certified1849 : Certified (graph core1849) (root 10) 0 0 :=
  of_native_maps core1849 DegreeOneSmallSpectrum1237.graph DegreeOneSmallSpectrum928.graph
    sourceMap1849 fusedMap1849 sourceMap1849_checked fusedMap1849_checked
    DegreeOneSmallComparisons.comparison1849
#print axioms sourceMap1849_checked
#print axioms fusedMap1849_checked
#print axioms certified1849
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
