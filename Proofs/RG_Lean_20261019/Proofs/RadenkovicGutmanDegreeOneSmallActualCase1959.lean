/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1959 : Family 10 := level10.get ⟨265,by decide⟩
def sourceMap1959 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1959 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1959_checked : acceptsGraphIso
    (source (graph core1959) (root 10) 0 0) DegreeOneSmallSpectrum1144.graph sourceMap1959=true := by decide +kernel
theorem fusedMap1959_checked : acceptsGraphIso
    (fused (graph core1959) (root 10) 0 0) DegreeOneSmallSpectrum1287.graph fusedMap1959=true := by decide +kernel
theorem certified1959 : Certified (graph core1959) (root 10) 0 0 :=
  of_native_maps core1959 DegreeOneSmallSpectrum1144.graph DegreeOneSmallSpectrum1287.graph
    sourceMap1959 fusedMap1959 sourceMap1959_checked fusedMap1959_checked
    DegreeOneSmallComparisons.comparison1959
#print axioms sourceMap1959_checked
#print axioms fusedMap1959_checked
#print axioms certified1959
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
