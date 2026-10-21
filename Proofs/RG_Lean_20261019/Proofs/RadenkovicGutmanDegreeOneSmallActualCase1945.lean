/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1945 : Family 10 := level10.get ⟨244,by decide⟩
def sourceMap1945 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1945 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1945_checked : acceptsGraphIso
    (source (graph core1945) (root 10) 0 0) DegreeOneSmallSpectrum1160.graph sourceMap1945=true := by decide +kernel
theorem fusedMap1945_checked : acceptsGraphIso
    (fused (graph core1945) (root 10) 0 0) DegreeOneSmallSpectrum1210.graph fusedMap1945=true := by decide +kernel
theorem certified1945 : Certified (graph core1945) (root 10) 0 0 :=
  of_native_maps core1945 DegreeOneSmallSpectrum1160.graph DegreeOneSmallSpectrum1210.graph
    sourceMap1945 fusedMap1945 sourceMap1945_checked fusedMap1945_checked
    DegreeOneSmallComparisons.comparison1945
#print axioms sourceMap1945_checked
#print axioms fusedMap1945_checked
#print axioms certified1945
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
