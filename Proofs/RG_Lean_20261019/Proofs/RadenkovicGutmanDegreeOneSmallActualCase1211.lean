/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1211 : Family 9 := level9.get ⟨9,by decide⟩
def sourceMap1211 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1211 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1211_checked : acceptsGraphIso
    (source (graph core1211) (root 9) 0 0) DegreeOneSmallSpectrum420.graph sourceMap1211=true := by decide +kernel
theorem fusedMap1211_checked : acceptsGraphIso
    (fused (graph core1211) (root 9) 0 0) DegreeOneSmallSpectrum370.graph fusedMap1211=true := by decide +kernel
theorem certified1211 : Certified (graph core1211) (root 9) 0 0 :=
  of_native_maps core1211 DegreeOneSmallSpectrum420.graph DegreeOneSmallSpectrum370.graph
    sourceMap1211 fusedMap1211 sourceMap1211_checked fusedMap1211_checked
    DegreeOneSmallComparisons.comparison1211
#print axioms sourceMap1211_checked
#print axioms fusedMap1211_checked
#print axioms certified1211
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
