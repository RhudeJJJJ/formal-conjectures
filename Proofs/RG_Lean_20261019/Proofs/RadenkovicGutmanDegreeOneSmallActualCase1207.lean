/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1207 : Family 9 := level9.get ⟨6,by decide⟩
def sourceMap1207 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1207 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap1207_checked : acceptsGraphIso
    (source (graph core1207) (root 9) 0 0) DegreeOneSmallSpectrum372.graph sourceMap1207=true := by decide +kernel
theorem fusedMap1207_checked : acceptsGraphIso
    (fused (graph core1207) (root 9) 0 0) DegreeOneSmallSpectrum396.graph fusedMap1207=true := by decide +kernel
theorem certified1207 : Certified (graph core1207) (root 9) 0 0 :=
  of_native_maps core1207 DegreeOneSmallSpectrum372.graph DegreeOneSmallSpectrum396.graph
    sourceMap1207 fusedMap1207 sourceMap1207_checked fusedMap1207_checked
    DegreeOneSmallComparisons.comparison1207
#print axioms sourceMap1207_checked
#print axioms fusedMap1207_checked
#print axioms certified1207
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
