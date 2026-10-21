/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1503 : Family 9 := level9.get ⟨232,by decide⟩
def sourceMap1503 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1503 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1503_checked : acceptsGraphIso
    (source (graph core1503) (root 9) 0 0) DegreeOneSmallSpectrum740.graph sourceMap1503=true := by decide +kernel
theorem fusedMap1503_checked : acceptsGraphIso
    (fused (graph core1503) (root 9) 0 0) DegreeOneSmallSpectrum543.graph fusedMap1503=true := by decide +kernel
theorem certified1503 : Certified (graph core1503) (root 9) 0 0 :=
  of_native_maps core1503 DegreeOneSmallSpectrum740.graph DegreeOneSmallSpectrum543.graph
    sourceMap1503 fusedMap1503 sourceMap1503_checked fusedMap1503_checked
    DegreeOneSmallComparisons.comparison1503
#print axioms sourceMap1503_checked
#print axioms fusedMap1503_checked
#print axioms certified1503
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
