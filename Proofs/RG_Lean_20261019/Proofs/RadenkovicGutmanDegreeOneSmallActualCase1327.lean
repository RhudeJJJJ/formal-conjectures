/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1327 : Family 9 := level9.get ⟨85,by decide⟩
def sourceMap1327 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1327 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1327_checked : acceptsGraphIso
    (source (graph core1327) (root 9) 0 0) DegreeOneSmallSpectrum467.graph sourceMap1327=true := by decide +kernel
theorem fusedMap1327_checked : acceptsGraphIso
    (fused (graph core1327) (root 9) 0 0) DegreeOneSmallSpectrum560.graph fusedMap1327=true := by decide +kernel
theorem certified1327 : Certified (graph core1327) (root 9) 0 0 :=
  of_native_maps core1327 DegreeOneSmallSpectrum467.graph DegreeOneSmallSpectrum560.graph
    sourceMap1327 fusedMap1327 sourceMap1327_checked fusedMap1327_checked
    DegreeOneSmallComparisons.comparison1327
#print axioms sourceMap1327_checked
#print axioms fusedMap1327_checked
#print axioms certified1327
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
