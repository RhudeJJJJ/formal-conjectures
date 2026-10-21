/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1051 : Family 8 := level8.get ⟨122,by decide⟩
def sourceMap1051 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1051 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1051_checked : acceptsGraphIso
    (source (graph core1051) (root 8) 0 0) DegreeOneSmallSpectrum273.graph sourceMap1051=true := by decide +kernel
theorem fusedMap1051_checked : acceptsGraphIso
    (fused (graph core1051) (root 8) 0 0) DegreeOneSmallSpectrum314.graph fusedMap1051=true := by decide +kernel
theorem certified1051 : Certified (graph core1051) (root 8) 0 0 :=
  of_native_maps core1051 DegreeOneSmallSpectrum273.graph DegreeOneSmallSpectrum314.graph
    sourceMap1051 fusedMap1051 sourceMap1051_checked fusedMap1051_checked
    DegreeOneSmallComparisons.comparison1051
#print axioms sourceMap1051_checked
#print axioms fusedMap1051_checked
#print axioms certified1051
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
