/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1067 : Family 8 := level8.get ⟨134,by decide⟩
def sourceMap1067 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 8 0 0 v)
def fusedMap1067 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap1067_checked : acceptsGraphIso
    (source (graph core1067) (root 8) 0 0) DegreeOneSmallSpectrum294.graph sourceMap1067=true := by decide +kernel
theorem fusedMap1067_checked : acceptsGraphIso
    (fused (graph core1067) (root 8) 0 0) DegreeOneSmallSpectrum324.graph fusedMap1067=true := by decide +kernel
theorem certified1067 : Certified (graph core1067) (root 8) 0 0 :=
  of_native_maps core1067 DegreeOneSmallSpectrum294.graph DegreeOneSmallSpectrum324.graph
    sourceMap1067 fusedMap1067 sourceMap1067_checked fusedMap1067_checked
    DegreeOneSmallComparisons.comparison1067
#print axioms sourceMap1067_checked
#print axioms fusedMap1067_checked
#print axioms certified1067
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
