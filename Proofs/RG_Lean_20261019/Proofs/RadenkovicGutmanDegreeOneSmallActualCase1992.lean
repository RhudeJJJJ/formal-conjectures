/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1992 : Family 10 := level10.get ⟨319,by decide⟩
def sourceMap1992 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1992 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1992_checked : acceptsGraphIso
    (source (graph core1992) (root 10) 0 0) DegreeOneSmallSpectrum1129.graph sourceMap1992=true := by decide +kernel
theorem fusedMap1992_checked : acceptsGraphIso
    (fused (graph core1992) (root 10) 0 0) DegreeOneSmallSpectrum1390.graph fusedMap1992=true := by decide +kernel
theorem certified1992 : Certified (graph core1992) (root 10) 0 0 :=
  of_native_maps core1992 DegreeOneSmallSpectrum1129.graph DegreeOneSmallSpectrum1390.graph
    sourceMap1992 fusedMap1992 sourceMap1992_checked fusedMap1992_checked
    DegreeOneSmallComparisons.comparison1992
#print axioms sourceMap1992_checked
#print axioms fusedMap1992_checked
#print axioms certified1992
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
