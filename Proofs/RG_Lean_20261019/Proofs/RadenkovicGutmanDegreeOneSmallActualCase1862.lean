/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1862 : Family 10 := level10.get ⟨121,by decide⟩
def sourceMap1862 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1862 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1862_checked : acceptsGraphIso
    (source (graph core1862) (root 10) 0 0) DegreeOneSmallSpectrum1281.graph sourceMap1862=true := by decide +kernel
theorem fusedMap1862_checked : acceptsGraphIso
    (fused (graph core1862) (root 10) 0 0) DegreeOneSmallSpectrum947.graph fusedMap1862=true := by decide +kernel
theorem certified1862 : Certified (graph core1862) (root 10) 0 0 :=
  of_native_maps core1862 DegreeOneSmallSpectrum1281.graph DegreeOneSmallSpectrum947.graph
    sourceMap1862 fusedMap1862 sourceMap1862_checked fusedMap1862_checked
    DegreeOneSmallComparisons.comparison1862
#print axioms sourceMap1862_checked
#print axioms fusedMap1862_checked
#print axioms certified1862
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
