/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1975 : Family 10 := level10.get ⟨295,by decide⟩
def sourceMap1975 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1975 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1975_checked : acceptsGraphIso
    (source (graph core1975) (root 10) 0 0) DegreeOneSmallSpectrum1204.graph sourceMap1975=true := by decide +kernel
theorem fusedMap1975_checked : acceptsGraphIso
    (fused (graph core1975) (root 10) 0 0) DegreeOneSmallSpectrum1347.graph fusedMap1975=true := by decide +kernel
theorem certified1975 : Certified (graph core1975) (root 10) 0 0 :=
  of_native_maps core1975 DegreeOneSmallSpectrum1204.graph DegreeOneSmallSpectrum1347.graph
    sourceMap1975 fusedMap1975 sourceMap1975_checked fusedMap1975_checked
    DegreeOneSmallComparisons.comparison1975
#print axioms sourceMap1975_checked
#print axioms fusedMap1975_checked
#print axioms certified1975
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
