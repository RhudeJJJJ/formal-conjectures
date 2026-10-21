/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1883 : Family 10 := level10.get ⟨149,by decide⟩
def sourceMap1883 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1883 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1883_checked : acceptsGraphIso
    (source (graph core1883) (root 10) 0 0) DegreeOneSmallSpectrum1181.graph sourceMap1883=true := by decide +kernel
theorem fusedMap1883_checked : acceptsGraphIso
    (fused (graph core1883) (root 10) 0 0) DegreeOneSmallSpectrum963.graph fusedMap1883=true := by decide +kernel
theorem certified1883 : Certified (graph core1883) (root 10) 0 0 :=
  of_native_maps core1883 DegreeOneSmallSpectrum1181.graph DegreeOneSmallSpectrum963.graph
    sourceMap1883 fusedMap1883 sourceMap1883_checked fusedMap1883_checked
    DegreeOneSmallComparisons.comparison1883
#print axioms sourceMap1883_checked
#print axioms fusedMap1883_checked
#print axioms certified1883
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
