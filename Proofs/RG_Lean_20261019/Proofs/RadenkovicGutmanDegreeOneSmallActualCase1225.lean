/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1225 : Family 9 := level9.get ⟨17,by decide⟩
def sourceMap1225 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1225 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1225_checked : acceptsGraphIso
    (source (graph core1225) (root 9) 0 0) DegreeOneSmallSpectrum486.graph sourceMap1225=true := by decide +kernel
theorem fusedMap1225_checked : acceptsGraphIso
    (fused (graph core1225) (root 9) 0 0) DegreeOneSmallSpectrum380.graph fusedMap1225=true := by decide +kernel
theorem certified1225 : Certified (graph core1225) (root 9) 0 0 :=
  of_native_maps core1225 DegreeOneSmallSpectrum486.graph DegreeOneSmallSpectrum380.graph
    sourceMap1225 fusedMap1225 sourceMap1225_checked fusedMap1225_checked
    DegreeOneSmallComparisons.comparison1225
#print axioms sourceMap1225_checked
#print axioms fusedMap1225_checked
#print axioms certified1225
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
