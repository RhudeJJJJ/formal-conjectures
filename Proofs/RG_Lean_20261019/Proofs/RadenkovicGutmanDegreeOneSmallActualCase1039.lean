/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1039 : Family 8 := level8.get ⟨116,by decide⟩
def sourceMap1039 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1039 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1039_checked : acceptsGraphIso
    (source (graph core1039) (root 8) 0 0) DegreeOneSmallSpectrum286.graph sourceMap1039=true := by decide +kernel
theorem fusedMap1039_checked : acceptsGraphIso
    (fused (graph core1039) (root 8) 0 0) DegreeOneSmallSpectrum300.graph fusedMap1039=true := by decide +kernel
theorem certified1039 : Certified (graph core1039) (root 8) 0 0 :=
  of_native_maps core1039 DegreeOneSmallSpectrum286.graph DegreeOneSmallSpectrum300.graph
    sourceMap1039 fusedMap1039 sourceMap1039_checked fusedMap1039_checked
    DegreeOneSmallComparisons.comparison1039
#print axioms sourceMap1039_checked
#print axioms fusedMap1039_checked
#print axioms certified1039
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
