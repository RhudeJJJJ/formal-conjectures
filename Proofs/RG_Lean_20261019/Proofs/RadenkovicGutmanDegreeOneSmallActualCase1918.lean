/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1918 : Family 10 := level10.get ⟨206,by decide⟩
def sourceMap1918 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap1918 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1918_checked : acceptsGraphIso
    (source (graph core1918) (root 10) 0 0) DegreeOneSmallSpectrum1064.graph sourceMap1918=true := by decide +kernel
theorem fusedMap1918_checked : acceptsGraphIso
    (fused (graph core1918) (root 10) 0 0) DegreeOneSmallSpectrum1081.graph fusedMap1918=true := by decide +kernel
theorem certified1918 : Certified (graph core1918) (root 10) 0 0 :=
  of_native_maps core1918 DegreeOneSmallSpectrum1064.graph DegreeOneSmallSpectrum1081.graph
    sourceMap1918 fusedMap1918 sourceMap1918_checked fusedMap1918_checked
    DegreeOneSmallComparisons.comparison1918
#print axioms sourceMap1918_checked
#print axioms fusedMap1918_checked
#print axioms certified1918
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
