/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1521 : Family 9 := level9.get ⟨254,by decide⟩
def sourceMap1521 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1521 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1521_checked : acceptsGraphIso
    (source (graph core1521) (root 9) 0 0) DegreeOneSmallSpectrum766.graph sourceMap1521=true := by decide +kernel
theorem fusedMap1521_checked : acceptsGraphIso
    (fused (graph core1521) (root 9) 0 0) DegreeOneSmallSpectrum564.graph fusedMap1521=true := by decide +kernel
theorem certified1521 : Certified (graph core1521) (root 9) 0 0 :=
  of_native_maps core1521 DegreeOneSmallSpectrum766.graph DegreeOneSmallSpectrum564.graph
    sourceMap1521 fusedMap1521 sourceMap1521_checked fusedMap1521_checked
    DegreeOneSmallComparisons.comparison1521
#print axioms sourceMap1521_checked
#print axioms fusedMap1521_checked
#print axioms certified1521
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
