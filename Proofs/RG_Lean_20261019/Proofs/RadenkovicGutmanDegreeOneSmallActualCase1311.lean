/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1311 : Family 9 := level9.get ⟨75,by decide⟩
def sourceMap1311 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1311 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1311_checked : acceptsGraphIso
    (source (graph core1311) (root 9) 0 0) DegreeOneSmallSpectrum485.graph sourceMap1311=true := by decide +kernel
theorem fusedMap1311_checked : acceptsGraphIso
    (fused (graph core1311) (root 9) 0 0) DegreeOneSmallSpectrum528.graph fusedMap1311=true := by decide +kernel
theorem certified1311 : Certified (graph core1311) (root 9) 0 0 :=
  of_native_maps core1311 DegreeOneSmallSpectrum485.graph DegreeOneSmallSpectrum528.graph
    sourceMap1311 fusedMap1311 sourceMap1311_checked fusedMap1311_checked
    DegreeOneSmallComparisons.comparison1311
#print axioms sourceMap1311_checked
#print axioms fusedMap1311_checked
#print axioms certified1311
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
