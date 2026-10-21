/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1629 : Family 9 := level9.get ⟨370,by decide⟩
def sourceMap1629 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1629 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1629_checked : acceptsGraphIso
    (source (graph core1629) (root 9) 0 0) DegreeOneSmallSpectrum719.graph sourceMap1629=true := by decide +kernel
theorem fusedMap1629_checked : acceptsGraphIso
    (fused (graph core1629) (root 9) 0 0) DegreeOneSmallSpectrum728.graph fusedMap1629=true := by decide +kernel
theorem certified1629 : Certified (graph core1629) (root 9) 0 0 :=
  of_native_maps core1629 DegreeOneSmallSpectrum719.graph DegreeOneSmallSpectrum728.graph
    sourceMap1629 fusedMap1629 sourceMap1629_checked fusedMap1629_checked
    DegreeOneSmallComparisons.comparison1629
#print axioms sourceMap1629_checked
#print axioms fusedMap1629_checked
#print axioms certified1629
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
