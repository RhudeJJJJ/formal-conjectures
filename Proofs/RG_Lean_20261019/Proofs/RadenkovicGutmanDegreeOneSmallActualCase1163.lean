/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1163 : Family 8 := level8.get ⟨207,by decide⟩
def sourceMap1163 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1163 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1163_checked : acceptsGraphIso
    (source (graph core1163) (root 8) 0 0) DegreeOneSmallSpectrum362.graph sourceMap1163=true := by decide +kernel
theorem fusedMap1163_checked : acceptsGraphIso
    (fused (graph core1163) (root 8) 0 0) DegreeOneSmallSpectrum267.graph fusedMap1163=true := by decide +kernel
theorem certified1163 : Certified (graph core1163) (root 8) 0 0 :=
  of_native_maps core1163 DegreeOneSmallSpectrum362.graph DegreeOneSmallSpectrum267.graph
    sourceMap1163 fusedMap1163 sourceMap1163_checked fusedMap1163_checked
    DegreeOneSmallComparisons.comparison1163
#print axioms sourceMap1163_checked
#print axioms fusedMap1163_checked
#print axioms certified1163
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
