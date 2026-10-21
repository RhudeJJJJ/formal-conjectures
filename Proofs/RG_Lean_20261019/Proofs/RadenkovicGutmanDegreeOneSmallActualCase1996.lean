/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1996 : Family 10 := level10.get ⟨326,by decide⟩
def sourceMap1996 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1996 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1996_checked : acceptsGraphIso
    (source (graph core1996) (root 10) 0 0) DegreeOneSmallSpectrum1235.graph sourceMap1996=true := by decide +kernel
theorem fusedMap1996_checked : acceptsGraphIso
    (fused (graph core1996) (root 10) 0 0) DegreeOneSmallSpectrum1414.graph fusedMap1996=true := by decide +kernel
theorem certified1996 : Certified (graph core1996) (root 10) 0 0 :=
  of_native_maps core1996 DegreeOneSmallSpectrum1235.graph DegreeOneSmallSpectrum1414.graph
    sourceMap1996 fusedMap1996 sourceMap1996_checked fusedMap1996_checked
    DegreeOneSmallComparisons.comparison1996
#print axioms sourceMap1996_checked
#print axioms fusedMap1996_checked
#print axioms certified1996
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
