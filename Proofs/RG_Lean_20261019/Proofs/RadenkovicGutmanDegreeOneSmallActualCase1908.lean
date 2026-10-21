/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1908 : Family 10 := level10.get ⟨193,by decide⟩
def sourceMap1908 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1908 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1908_checked : acceptsGraphIso
    (source (graph core1908) (root 10) 0 0) DegreeOneSmallSpectrum999.graph sourceMap1908=true := by decide +kernel
theorem fusedMap1908_checked : acceptsGraphIso
    (fused (graph core1908) (root 10) 0 0) DegreeOneSmallSpectrum1007.graph fusedMap1908=true := by decide +kernel
theorem certified1908 : Certified (graph core1908) (root 10) 0 0 :=
  of_native_maps core1908 DegreeOneSmallSpectrum999.graph DegreeOneSmallSpectrum1007.graph
    sourceMap1908 fusedMap1908 sourceMap1908_checked fusedMap1908_checked
    DegreeOneSmallComparisons.comparison1908
#print axioms sourceMap1908_checked
#print axioms fusedMap1908_checked
#print axioms certified1908
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
