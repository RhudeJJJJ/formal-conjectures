/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1087 : Family 8 := level8.get ⟨144,by decide⟩
def sourceMap1087 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1087 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1087_checked : acceptsGraphIso
    (source (graph core1087) (root 8) 0 0) DegreeOneSmallSpectrum279.graph sourceMap1087=true := by decide +kernel
theorem fusedMap1087_checked : acceptsGraphIso
    (fused (graph core1087) (root 8) 0 0) DegreeOneSmallSpectrum337.graph fusedMap1087=true := by decide +kernel
theorem certified1087 : Certified (graph core1087) (root 8) 0 0 :=
  of_native_maps core1087 DegreeOneSmallSpectrum279.graph DegreeOneSmallSpectrum337.graph
    sourceMap1087 fusedMap1087 sourceMap1087_checked fusedMap1087_checked
    DegreeOneSmallComparisons.comparison1087
#print axioms sourceMap1087_checked
#print axioms fusedMap1087_checked
#print axioms certified1087
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
