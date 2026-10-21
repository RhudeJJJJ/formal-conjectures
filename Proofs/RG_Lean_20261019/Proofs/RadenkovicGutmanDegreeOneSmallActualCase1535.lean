/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1535 : Family 9 := level9.get ⟨263,by decide⟩
def sourceMap1535 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1535 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1535_checked : acceptsGraphIso
    (source (graph core1535) (root 9) 0 0) DegreeOneSmallSpectrum727.graph sourceMap1535=true := by decide +kernel
theorem fusedMap1535_checked : acceptsGraphIso
    (fused (graph core1535) (root 9) 0 0) DegreeOneSmallSpectrum573.graph fusedMap1535=true := by decide +kernel
theorem certified1535 : Certified (graph core1535) (root 9) 0 0 :=
  of_native_maps core1535 DegreeOneSmallSpectrum727.graph DegreeOneSmallSpectrum573.graph
    sourceMap1535 fusedMap1535 sourceMap1535_checked fusedMap1535_checked
    DegreeOneSmallComparisons.comparison1535
#print axioms sourceMap1535_checked
#print axioms fusedMap1535_checked
#print axioms certified1535
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
