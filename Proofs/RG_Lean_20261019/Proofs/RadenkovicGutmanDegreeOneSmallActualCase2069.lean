/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2069 : Family 10 := level10.get ⟨450,by decide⟩
def sourceMap2069 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2069 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2069_checked : acceptsGraphIso
    (source (graph core2069) (root 10) 0 0) DegreeOneSmallSpectrum1097.graph sourceMap2069=true := by decide +kernel
theorem fusedMap2069_checked : acceptsGraphIso
    (fused (graph core2069) (root 10) 0 0) DegreeOneSmallSpectrum1491.graph fusedMap2069=true := by decide +kernel
theorem certified2069 : Certified (graph core2069) (root 10) 0 0 :=
  of_native_maps core2069 DegreeOneSmallSpectrum1097.graph DegreeOneSmallSpectrum1491.graph
    sourceMap2069 fusedMap2069 sourceMap2069_checked fusedMap2069_checked
    DegreeOneSmallComparisons.comparison2069
#print axioms sourceMap2069_checked
#print axioms fusedMap2069_checked
#print axioms certified2069
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
