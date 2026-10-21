/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1195 : Family 9 := level9.get ⟨0,by decide⟩
def sourceMap1195 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,3,2,1,0,7,8,9,10,11,5,6] (sourceLabel 9 0 0 v)
def fusedMap1195 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap1195_checked : acceptsGraphIso
    (source (graph core1195) (root 9) 0 0) DegreeOneSmallSpectrum378.graph sourceMap1195=true := by decide +kernel
theorem fusedMap1195_checked : acceptsGraphIso
    (fused (graph core1195) (root 9) 0 0) DegreeOneSmallSpectrum369.graph fusedMap1195=true := by decide +kernel
theorem certified1195 : Certified (graph core1195) (root 9) 0 0 :=
  of_native_maps core1195 DegreeOneSmallSpectrum378.graph DegreeOneSmallSpectrum369.graph
    sourceMap1195 fusedMap1195 sourceMap1195_checked fusedMap1195_checked
    DegreeOneSmallComparisons.comparison1195
#print axioms sourceMap1195_checked
#print axioms fusedMap1195_checked
#print axioms certified1195
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
