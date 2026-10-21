/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1143 : Family 8 := level8.get ⟨191,by decide⟩
def sourceMap1143 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (sourceLabel 8 0 0 v)
def fusedMap1143 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1143_checked : acceptsGraphIso
    (source (graph core1143) (root 8) 0 0) DegreeOneSmallSpectrum357.graph sourceMap1143=true := by decide +kernel
theorem fusedMap1143_checked : acceptsGraphIso
    (fused (graph core1143) (root 8) 0 0) DegreeOneSmallSpectrum235.graph fusedMap1143=true := by decide +kernel
theorem certified1143 : Certified (graph core1143) (root 8) 0 0 :=
  of_native_maps core1143 DegreeOneSmallSpectrum357.graph DegreeOneSmallSpectrum235.graph
    sourceMap1143 fusedMap1143 sourceMap1143_checked fusedMap1143_checked
    DegreeOneSmallComparisons.comparison1143
#print axioms sourceMap1143_checked
#print axioms fusedMap1143_checked
#print axioms certified1143
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
