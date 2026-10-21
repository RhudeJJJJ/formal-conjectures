/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1811 : Family 10 := level10.get ⟨54,by decide⟩
def sourceMap1811 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1811 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1811_checked : acceptsGraphIso
    (source (graph core1811) (root 10) 0 0) DegreeOneSmallSpectrum1030.graph sourceMap1811=true := by decide +kernel
theorem fusedMap1811_checked : acceptsGraphIso
    (fused (graph core1811) (root 10) 0 0) DegreeOneSmallSpectrum863.graph fusedMap1811=true := by decide +kernel
theorem certified1811 : Certified (graph core1811) (root 10) 0 0 :=
  of_native_maps core1811 DegreeOneSmallSpectrum1030.graph DegreeOneSmallSpectrum863.graph
    sourceMap1811 fusedMap1811 sourceMap1811_checked fusedMap1811_checked
    DegreeOneSmallComparisons.comparison1811
#print axioms sourceMap1811_checked
#print axioms fusedMap1811_checked
#print axioms certified1811
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
