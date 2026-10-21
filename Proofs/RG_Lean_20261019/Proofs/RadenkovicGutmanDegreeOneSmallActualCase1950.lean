/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1950 : Family 10 := level10.get ⟨251,by decide⟩
def sourceMap1950 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap1950 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1950_checked : acceptsGraphIso
    (source (graph core1950) (root 10) 0 0) DegreeOneSmallSpectrum1217.graph sourceMap1950=true := by decide +kernel
theorem fusedMap1950_checked : acceptsGraphIso
    (fused (graph core1950) (root 10) 0 0) DegreeOneSmallSpectrum1247.graph fusedMap1950=true := by decide +kernel
theorem certified1950 : Certified (graph core1950) (root 10) 0 0 :=
  of_native_maps core1950 DegreeOneSmallSpectrum1217.graph DegreeOneSmallSpectrum1247.graph
    sourceMap1950 fusedMap1950 sourceMap1950_checked fusedMap1950_checked
    DegreeOneSmallComparisons.comparison1950
#print axioms sourceMap1950_checked
#print axioms fusedMap1950_checked
#print axioms certified1950
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
