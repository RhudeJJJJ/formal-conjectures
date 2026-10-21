/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1287 : Family 9 := level9.get ⟨57,by decide⟩
def sourceMap1287 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1287 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1287_checked : acceptsGraphIso
    (source (graph core1287) (root 9) 0 0) DegreeOneSmallSpectrum470.graph sourceMap1287=true := by decide +kernel
theorem fusedMap1287_checked : acceptsGraphIso
    (fused (graph core1287) (root 9) 0 0) DegreeOneSmallSpectrum479.graph fusedMap1287=true := by decide +kernel
theorem certified1287 : Certified (graph core1287) (root 9) 0 0 :=
  of_native_maps core1287 DegreeOneSmallSpectrum470.graph DegreeOneSmallSpectrum479.graph
    sourceMap1287 fusedMap1287 sourceMap1287_checked fusedMap1287_checked
    DegreeOneSmallComparisons.comparison1287
#print axioms sourceMap1287_checked
#print axioms fusedMap1287_checked
#print axioms certified1287
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
