/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1271 : Family 9 := level9.get ⟨47,by decide⟩
def sourceMap1271 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1271 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1271_checked : acceptsGraphIso
    (source (graph core1271) (root 9) 0 0) DegreeOneSmallSpectrum418.graph sourceMap1271=true := by decide +kernel
theorem fusedMap1271_checked : acceptsGraphIso
    (fused (graph core1271) (root 9) 0 0) DegreeOneSmallSpectrum426.graph fusedMap1271=true := by decide +kernel
theorem certified1271 : Certified (graph core1271) (root 9) 0 0 :=
  of_native_maps core1271 DegreeOneSmallSpectrum418.graph DegreeOneSmallSpectrum426.graph
    sourceMap1271 fusedMap1271 sourceMap1271_checked fusedMap1271_checked
    DegreeOneSmallComparisons.comparison1271
#print axioms sourceMap1271_checked
#print axioms fusedMap1271_checked
#print axioms certified1271
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
