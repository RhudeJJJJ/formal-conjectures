/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1295 : Family 9 := level9.get ⟨62,by decide⟩
def sourceMap1295 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1295 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1295_checked : acceptsGraphIso
    (source (graph core1295) (root 9) 0 0) DegreeOneSmallSpectrum443.graph sourceMap1295=true := by decide +kernel
theorem fusedMap1295_checked : acceptsGraphIso
    (fused (graph core1295) (root 9) 0 0) DegreeOneSmallSpectrum497.graph fusedMap1295=true := by decide +kernel
theorem certified1295 : Certified (graph core1295) (root 9) 0 0 :=
  of_native_maps core1295 DegreeOneSmallSpectrum443.graph DegreeOneSmallSpectrum497.graph
    sourceMap1295 fusedMap1295 sourceMap1295_checked fusedMap1295_checked
    DegreeOneSmallComparisons.comparison1295
#print axioms sourceMap1295_checked
#print axioms fusedMap1295_checked
#print axioms certified1295
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
