/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1979 : Family 10 := level10.get ⟨300,by decide⟩
def sourceMap1979 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1979 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1979_checked : acceptsGraphIso
    (source (graph core1979) (root 10) 0 0) DegreeOneSmallSpectrum1128.graph sourceMap1979=true := by decide +kernel
theorem fusedMap1979_checked : acceptsGraphIso
    (fused (graph core1979) (root 10) 0 0) DegreeOneSmallSpectrum1345.graph fusedMap1979=true := by decide +kernel
theorem certified1979 : Certified (graph core1979) (root 10) 0 0 :=
  of_native_maps core1979 DegreeOneSmallSpectrum1128.graph DegreeOneSmallSpectrum1345.graph
    sourceMap1979 fusedMap1979 sourceMap1979_checked fusedMap1979_checked
    DegreeOneSmallComparisons.comparison1979
#print axioms sourceMap1979_checked
#print axioms fusedMap1979_checked
#print axioms certified1979
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
