/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1513 : Family 9 := level9.get ⟨241,by decide⟩
def sourceMap1513 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1513 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1513_checked : acceptsGraphIso
    (source (graph core1513) (root 9) 0 0) DegreeOneSmallSpectrum696.graph sourceMap1513=true := by decide +kernel
theorem fusedMap1513_checked : acceptsGraphIso
    (fused (graph core1513) (root 9) 0 0) DegreeOneSmallSpectrum554.graph fusedMap1513=true := by decide +kernel
theorem certified1513 : Certified (graph core1513) (root 9) 0 0 :=
  of_native_maps core1513 DegreeOneSmallSpectrum696.graph DegreeOneSmallSpectrum554.graph
    sourceMap1513 fusedMap1513 sourceMap1513_checked fusedMap1513_checked
    DegreeOneSmallComparisons.comparison1513
#print axioms sourceMap1513_checked
#print axioms fusedMap1513_checked
#print axioms certified1513
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
