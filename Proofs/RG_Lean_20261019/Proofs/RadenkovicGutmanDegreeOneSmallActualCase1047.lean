/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1047 : Family 8 := level8.get ⟨121,by decide⟩
def sourceMap1047 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1047 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1047_checked : acceptsGraphIso
    (source (graph core1047) (root 8) 0 0) DegreeOneSmallSpectrum268.graph sourceMap1047=true := by decide +kernel
theorem fusedMap1047_checked : acceptsGraphIso
    (fused (graph core1047) (root 8) 0 0) DegreeOneSmallSpectrum313.graph fusedMap1047=true := by decide +kernel
theorem certified1047 : Certified (graph core1047) (root 8) 0 0 :=
  of_native_maps core1047 DegreeOneSmallSpectrum268.graph DegreeOneSmallSpectrum313.graph
    sourceMap1047 fusedMap1047 sourceMap1047_checked fusedMap1047_checked
    DegreeOneSmallComparisons.comparison1047
#print axioms sourceMap1047_checked
#print axioms fusedMap1047_checked
#print axioms certified1047
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
