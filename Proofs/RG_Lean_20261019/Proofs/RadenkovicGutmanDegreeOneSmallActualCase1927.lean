/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1927 : Family 10 := level10.get ⟨219,by decide⟩
def sourceMap1927 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1927 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1927_checked : acceptsGraphIso
    (source (graph core1927) (root 10) 0 0) DegreeOneSmallSpectrum1102.graph sourceMap1927=true := by decide +kernel
theorem fusedMap1927_checked : acceptsGraphIso
    (fused (graph core1927) (root 10) 0 0) DegreeOneSmallSpectrum1111.graph fusedMap1927=true := by decide +kernel
theorem certified1927 : Certified (graph core1927) (root 10) 0 0 :=
  of_native_maps core1927 DegreeOneSmallSpectrum1102.graph DegreeOneSmallSpectrum1111.graph
    sourceMap1927 fusedMap1927 sourceMap1927_checked fusedMap1927_checked
    DegreeOneSmallComparisons.comparison1927
#print axioms sourceMap1927_checked
#print axioms fusedMap1927_checked
#print axioms certified1927
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
