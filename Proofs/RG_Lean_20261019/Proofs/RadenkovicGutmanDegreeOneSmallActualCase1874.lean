/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1874 : Family 10 := level10.get ⟨136,by decide⟩
def sourceMap1874 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1874 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1874_checked : acceptsGraphIso
    (source (graph core1874) (root 10) 0 0) DegreeOneSmallSpectrum1210.graph sourceMap1874=true := by decide +kernel
theorem fusedMap1874_checked : acceptsGraphIso
    (fused (graph core1874) (root 10) 0 0) DegreeOneSmallSpectrum963.graph fusedMap1874=true := by decide +kernel
theorem certified1874 : Certified (graph core1874) (root 10) 0 0 :=
  of_native_maps core1874 DegreeOneSmallSpectrum1210.graph DegreeOneSmallSpectrum963.graph
    sourceMap1874 fusedMap1874 sourceMap1874_checked fusedMap1874_checked
    DegreeOneSmallComparisons.comparison1874
#print axioms sourceMap1874_checked
#print axioms fusedMap1874_checked
#print axioms certified1874
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
