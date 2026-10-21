/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1541 : Family 9 := level9.get ⟨270,by decide⟩
def sourceMap1541 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1541 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1541_checked : acceptsGraphIso
    (source (graph core1541) (root 9) 0 0) DegreeOneSmallSpectrum708.graph sourceMap1541=true := by decide +kernel
theorem fusedMap1541_checked : acceptsGraphIso
    (fused (graph core1541) (root 9) 0 0) DegreeOneSmallSpectrum573.graph fusedMap1541=true := by decide +kernel
theorem certified1541 : Certified (graph core1541) (root 9) 0 0 :=
  of_native_maps core1541 DegreeOneSmallSpectrum708.graph DegreeOneSmallSpectrum573.graph
    sourceMap1541 fusedMap1541 sourceMap1541_checked fusedMap1541_checked
    DegreeOneSmallComparisons.comparison1541
#print axioms sourceMap1541_checked
#print axioms fusedMap1541_checked
#print axioms certified1541
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
