/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1325 : Family 9 := level9.get ⟨84,by decide⟩
def sourceMap1325 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1325 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1325_checked : acceptsGraphIso
    (source (graph core1325) (root 9) 0 0) DegreeOneSmallSpectrum462.graph sourceMap1325=true := by decide +kernel
theorem fusedMap1325_checked : acceptsGraphIso
    (fused (graph core1325) (root 9) 0 0) DegreeOneSmallSpectrum559.graph fusedMap1325=true := by decide +kernel
theorem certified1325 : Certified (graph core1325) (root 9) 0 0 :=
  of_native_maps core1325 DegreeOneSmallSpectrum462.graph DegreeOneSmallSpectrum559.graph
    sourceMap1325 fusedMap1325 sourceMap1325_checked fusedMap1325_checked
    DegreeOneSmallComparisons.comparison1325
#print axioms sourceMap1325_checked
#print axioms fusedMap1325_checked
#print axioms certified1325
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
