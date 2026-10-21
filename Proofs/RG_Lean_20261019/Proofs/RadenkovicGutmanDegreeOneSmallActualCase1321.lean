/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1321 : Family 9 := level9.get ⟨81,by decide⟩
def sourceMap1321 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1321 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1321_checked : acceptsGraphIso
    (source (graph core1321) (root 9) 0 0) DegreeOneSmallSpectrum474.graph sourceMap1321=true := by decide +kernel
theorem fusedMap1321_checked : acceptsGraphIso
    (fused (graph core1321) (root 9) 0 0) DegreeOneSmallSpectrum550.graph fusedMap1321=true := by decide +kernel
theorem certified1321 : Certified (graph core1321) (root 9) 0 0 :=
  of_native_maps core1321 DegreeOneSmallSpectrum474.graph DegreeOneSmallSpectrum550.graph
    sourceMap1321 fusedMap1321 sourceMap1321_checked fusedMap1321_checked
    DegreeOneSmallComparisons.comparison1321
#print axioms sourceMap1321_checked
#print axioms fusedMap1321_checked
#print axioms certified1321
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
