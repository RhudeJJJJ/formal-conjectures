/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1199 : Family 9 := level9.get ⟨2,by decide⟩
def sourceMap1199 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1199 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1199_checked : acceptsGraphIso
    (source (graph core1199) (root 9) 0 0) DegreeOneSmallSpectrum375.graph sourceMap1199=true := by decide +kernel
theorem fusedMap1199_checked : acceptsGraphIso
    (fused (graph core1199) (root 9) 0 0) DegreeOneSmallSpectrum386.graph fusedMap1199=true := by decide +kernel
theorem certified1199 : Certified (graph core1199) (root 9) 0 0 :=
  of_native_maps core1199 DegreeOneSmallSpectrum375.graph DegreeOneSmallSpectrum386.graph
    sourceMap1199 fusedMap1199 sourceMap1199_checked fusedMap1199_checked
    DegreeOneSmallComparisons.comparison1199
#print axioms sourceMap1199_checked
#print axioms fusedMap1199_checked
#print axioms certified1199
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
