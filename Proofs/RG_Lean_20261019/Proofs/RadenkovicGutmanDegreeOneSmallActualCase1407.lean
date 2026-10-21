/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1407 : Family 9 := level9.get ⟨151,by decide⟩
def sourceMap1407 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (sourceLabel 9 0 0 v)
def fusedMap1407 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1407_checked : acceptsGraphIso
    (source (graph core1407) (root 9) 0 0) DegreeOneSmallSpectrum660.graph sourceMap1407=true := by decide +kernel
theorem fusedMap1407_checked : acceptsGraphIso
    (fused (graph core1407) (root 9) 0 0) DegreeOneSmallSpectrum424.graph fusedMap1407=true := by decide +kernel
theorem certified1407 : Certified (graph core1407) (root 9) 0 0 :=
  of_native_maps core1407 DegreeOneSmallSpectrum660.graph DegreeOneSmallSpectrum424.graph
    sourceMap1407 fusedMap1407 sourceMap1407_checked fusedMap1407_checked
    DegreeOneSmallComparisons.comparison1407
#print axioms sourceMap1407_checked
#print axioms fusedMap1407_checked
#print axioms certified1407
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
