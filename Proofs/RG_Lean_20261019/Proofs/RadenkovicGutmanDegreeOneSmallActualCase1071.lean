/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1071 : Family 8 := level8.get ⟨136,by decide⟩
def sourceMap1071 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1071 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1071_checked : acceptsGraphIso
    (source (graph core1071) (root 8) 0 0) DegreeOneSmallSpectrum278.graph sourceMap1071=true := by decide +kernel
theorem fusedMap1071_checked : acceptsGraphIso
    (fused (graph core1071) (root 8) 0 0) DegreeOneSmallSpectrum329.graph fusedMap1071=true := by decide +kernel
theorem certified1071 : Certified (graph core1071) (root 8) 0 0 :=
  of_native_maps core1071 DegreeOneSmallSpectrum278.graph DegreeOneSmallSpectrum329.graph
    sourceMap1071 fusedMap1071 sourceMap1071_checked fusedMap1071_checked
    DegreeOneSmallComparisons.comparison1071
#print axioms sourceMap1071_checked
#print axioms fusedMap1071_checked
#print axioms certified1071
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
