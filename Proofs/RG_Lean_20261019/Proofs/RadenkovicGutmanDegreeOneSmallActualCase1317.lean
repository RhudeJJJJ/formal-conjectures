/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1317 : Family 9 := level9.get ⟨79,by decide⟩
def sourceMap1317 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1317 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1317_checked : acceptsGraphIso
    (source (graph core1317) (root 9) 0 0) DegreeOneSmallSpectrum487.graph sourceMap1317=true := by decide +kernel
theorem fusedMap1317_checked : acceptsGraphIso
    (fused (graph core1317) (root 9) 0 0) DegreeOneSmallSpectrum540.graph fusedMap1317=true := by decide +kernel
theorem certified1317 : Certified (graph core1317) (root 9) 0 0 :=
  of_native_maps core1317 DegreeOneSmallSpectrum487.graph DegreeOneSmallSpectrum540.graph
    sourceMap1317 fusedMap1317 sourceMap1317_checked fusedMap1317_checked
    DegreeOneSmallComparisons.comparison1317
#print axioms sourceMap1317_checked
#print axioms fusedMap1317_checked
#print axioms certified1317
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
