/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1990 : Family 10 := level10.get ⟨316,by decide⟩
def sourceMap1990 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1990 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1990_checked : acceptsGraphIso
    (source (graph core1990) (root 10) 0 0) DegreeOneSmallSpectrum1152.graph sourceMap1990=true := by decide +kernel
theorem fusedMap1990_checked : acceptsGraphIso
    (fused (graph core1990) (root 10) 0 0) DegreeOneSmallSpectrum1391.graph fusedMap1990=true := by decide +kernel
theorem certified1990 : Certified (graph core1990) (root 10) 0 0 :=
  of_native_maps core1990 DegreeOneSmallSpectrum1152.graph DegreeOneSmallSpectrum1391.graph
    sourceMap1990 fusedMap1990 sourceMap1990_checked fusedMap1990_checked
    DegreeOneSmallComparisons.comparison1990
#print axioms sourceMap1990_checked
#print axioms fusedMap1990_checked
#print axioms certified1990
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
