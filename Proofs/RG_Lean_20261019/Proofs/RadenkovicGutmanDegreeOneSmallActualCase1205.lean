/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1205 : Family 9 := level9.get ⟨5,by decide⟩
def sourceMap1205 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1205 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap1205_checked : acceptsGraphIso
    (source (graph core1205) (root 9) 0 0) DegreeOneSmallSpectrum373.graph sourceMap1205=true := by decide +kernel
theorem fusedMap1205_checked : acceptsGraphIso
    (fused (graph core1205) (root 9) 0 0) DegreeOneSmallSpectrum397.graph fusedMap1205=true := by decide +kernel
theorem certified1205 : Certified (graph core1205) (root 9) 0 0 :=
  of_native_maps core1205 DegreeOneSmallSpectrum373.graph DegreeOneSmallSpectrum397.graph
    sourceMap1205 fusedMap1205 sourceMap1205_checked fusedMap1205_checked
    DegreeOneSmallComparisons.comparison1205
#print axioms sourceMap1205_checked
#print axioms fusedMap1205_checked
#print axioms certified1205
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
