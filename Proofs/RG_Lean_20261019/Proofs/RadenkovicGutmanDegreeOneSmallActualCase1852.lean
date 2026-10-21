/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1852 : Family 10 := level10.get ⟨106,by decide⟩
def sourceMap1852 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1852 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1852_checked : acceptsGraphIso
    (source (graph core1852) (root 10) 0 0) DegreeOneSmallSpectrum1273.graph sourceMap1852=true := by decide +kernel
theorem fusedMap1852_checked : acceptsGraphIso
    (fused (graph core1852) (root 10) 0 0) DegreeOneSmallSpectrum931.graph fusedMap1852=true := by decide +kernel
theorem certified1852 : Certified (graph core1852) (root 10) 0 0 :=
  of_native_maps core1852 DegreeOneSmallSpectrum1273.graph DegreeOneSmallSpectrum931.graph
    sourceMap1852 fusedMap1852 sourceMap1852_checked fusedMap1852_checked
    DegreeOneSmallComparisons.comparison1852
#print axioms sourceMap1852_checked
#print axioms fusedMap1852_checked
#print axioms certified1852
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
