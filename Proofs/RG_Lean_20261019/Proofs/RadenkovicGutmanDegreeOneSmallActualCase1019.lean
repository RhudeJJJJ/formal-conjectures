/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1019 : Family 8 := level8.get ⟨109,by decide⟩
def sourceMap1019 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap1019 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1019_checked : acceptsGraphIso
    (source (graph core1019) (root 8) 0 0) DegreeOneSmallSpectrum273.graph sourceMap1019=true := by decide +kernel
theorem fusedMap1019_checked : acceptsGraphIso
    (fused (graph core1019) (root 8) 0 0) DegreeOneSmallSpectrum275.graph fusedMap1019=true := by decide +kernel
theorem certified1019 : Certified (graph core1019) (root 8) 0 0 :=
  of_native_maps core1019 DegreeOneSmallSpectrum273.graph DegreeOneSmallSpectrum275.graph
    sourceMap1019 fusedMap1019 sourceMap1019_checked fusedMap1019_checked
    DegreeOneSmallComparisons.comparison1019
#print axioms sourceMap1019_checked
#print axioms fusedMap1019_checked
#print axioms certified1019
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
