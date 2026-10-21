/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1281 : Family 9 := level9.get ⟨53,by decide⟩
def sourceMap1281 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1281 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1281_checked : acceptsGraphIso
    (source (graph core1281) (root 9) 0 0) DegreeOneSmallSpectrum447.graph sourceMap1281=true := by decide +kernel
theorem fusedMap1281_checked : acceptsGraphIso
    (fused (graph core1281) (root 9) 0 0) DegreeOneSmallSpectrum456.graph fusedMap1281=true := by decide +kernel
theorem certified1281 : Certified (graph core1281) (root 9) 0 0 :=
  of_native_maps core1281 DegreeOneSmallSpectrum447.graph DegreeOneSmallSpectrum456.graph
    sourceMap1281 fusedMap1281 sourceMap1281_checked fusedMap1281_checked
    DegreeOneSmallComparisons.comparison1281
#print axioms sourceMap1281_checked
#print axioms fusedMap1281_checked
#print axioms certified1281
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
