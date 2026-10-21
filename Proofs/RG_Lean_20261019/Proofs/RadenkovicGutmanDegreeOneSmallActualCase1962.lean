/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1962 : Family 10 := level10.get ⟨272,by decide⟩
def sourceMap1962 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap1962 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1962_checked : acceptsGraphIso
    (source (graph core1962) (root 10) 0 0) DegreeOneSmallSpectrum1278.graph sourceMap1962=true := by decide +kernel
theorem fusedMap1962_checked : acceptsGraphIso
    (fused (graph core1962) (root 10) 0 0) DegreeOneSmallSpectrum1275.graph fusedMap1962=true := by decide +kernel
theorem certified1962 : Certified (graph core1962) (root 10) 0 0 :=
  of_native_maps core1962 DegreeOneSmallSpectrum1278.graph DegreeOneSmallSpectrum1275.graph
    sourceMap1962 fusedMap1962 sourceMap1962_checked fusedMap1962_checked
    DegreeOneSmallComparisons.comparison1962
#print axioms sourceMap1962_checked
#print axioms fusedMap1962_checked
#print axioms certified1962
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
