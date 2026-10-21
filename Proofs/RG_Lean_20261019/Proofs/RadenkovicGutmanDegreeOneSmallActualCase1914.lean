/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1914 : Family 10 := level10.get ⟨201,by decide⟩
def sourceMap1914 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1914 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1914_checked : acceptsGraphIso
    (source (graph core1914) (root 10) 0 0) DegreeOneSmallSpectrum1041.graph sourceMap1914=true := by decide +kernel
theorem fusedMap1914_checked : acceptsGraphIso
    (fused (graph core1914) (root 10) 0 0) DegreeOneSmallSpectrum1044.graph fusedMap1914=true := by decide +kernel
theorem certified1914 : Certified (graph core1914) (root 10) 0 0 :=
  of_native_maps core1914 DegreeOneSmallSpectrum1041.graph DegreeOneSmallSpectrum1044.graph
    sourceMap1914 fusedMap1914 sourceMap1914_checked fusedMap1914_checked
    DegreeOneSmallComparisons.comparison1914
#print axioms sourceMap1914_checked
#print axioms fusedMap1914_checked
#print axioms certified1914
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
