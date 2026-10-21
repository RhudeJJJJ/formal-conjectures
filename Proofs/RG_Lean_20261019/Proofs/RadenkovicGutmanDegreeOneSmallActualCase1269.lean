/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1269 : Family 9 := level9.get ⟨46,by decide⟩
def sourceMap1269 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1269 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1269_checked : acceptsGraphIso
    (source (graph core1269) (root 9) 0 0) DegreeOneSmallSpectrum419.graph sourceMap1269=true := by decide +kernel
theorem fusedMap1269_checked : acceptsGraphIso
    (fused (graph core1269) (root 9) 0 0) DegreeOneSmallSpectrum427.graph fusedMap1269=true := by decide +kernel
theorem certified1269 : Certified (graph core1269) (root 9) 0 0 :=
  of_native_maps core1269 DegreeOneSmallSpectrum419.graph DegreeOneSmallSpectrum427.graph
    sourceMap1269 fusedMap1269 sourceMap1269_checked fusedMap1269_checked
    DegreeOneSmallComparisons.comparison1269
#print axioms sourceMap1269_checked
#print axioms fusedMap1269_checked
#print axioms certified1269
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
