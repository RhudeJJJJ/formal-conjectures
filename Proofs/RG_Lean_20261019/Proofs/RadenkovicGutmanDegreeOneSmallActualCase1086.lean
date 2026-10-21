/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1086 : Family 8 := level8.get ⟨142,by decide⟩
def sourceMap1086 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1086 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1086_checked : acceptsGraphIso
    (source (graph core1086) (root 8) 1 1) DegreeOneSmallSpectrum1919.graph sourceMap1086=true := by decide +kernel
theorem fusedMap1086_checked : acceptsGraphIso
    (fused (graph core1086) (root 8) 1 1) DegreeOneSmallSpectrum1358.graph fusedMap1086=true := by decide +kernel
theorem certified1086 : Certified (graph core1086) (root 8) 1 1 :=
  of_native_maps core1086 DegreeOneSmallSpectrum1919.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1086 fusedMap1086 sourceMap1086_checked fusedMap1086_checked
    DegreeOneSmallComparisons.comparison1086
#print axioms sourceMap1086_checked
#print axioms fusedMap1086_checked
#print axioms certified1086
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
