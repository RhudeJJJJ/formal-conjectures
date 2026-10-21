/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1930 : Family 10 := level10.get ⟨223,by decide⟩
def sourceMap1930 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1930 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1930_checked : acceptsGraphIso
    (source (graph core1930) (root 10) 0 0) DegreeOneSmallSpectrum1126.graph sourceMap1930=true := by decide +kernel
theorem fusedMap1930_checked : acceptsGraphIso
    (fused (graph core1930) (root 10) 0 0) DegreeOneSmallSpectrum1135.graph fusedMap1930=true := by decide +kernel
theorem certified1930 : Certified (graph core1930) (root 10) 0 0 :=
  of_native_maps core1930 DegreeOneSmallSpectrum1126.graph DegreeOneSmallSpectrum1135.graph
    sourceMap1930 fusedMap1930 sourceMap1930_checked fusedMap1930_checked
    DegreeOneSmallComparisons.comparison1930
#print axioms sourceMap1930_checked
#print axioms fusedMap1930_checked
#print axioms certified1930
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
