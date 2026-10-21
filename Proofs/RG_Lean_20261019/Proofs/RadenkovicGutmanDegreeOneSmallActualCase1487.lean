/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1487 : Family 9 := level9.get ⟨219,by decide⟩
def sourceMap1487 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1487 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1487_checked : acceptsGraphIso
    (source (graph core1487) (root 9) 0 0) DegreeOneSmallSpectrum738.graph sourceMap1487=true := by decide +kernel
theorem fusedMap1487_checked : acceptsGraphIso
    (fused (graph core1487) (root 9) 0 0) DegreeOneSmallSpectrum527.graph fusedMap1487=true := by decide +kernel
theorem certified1487 : Certified (graph core1487) (root 9) 0 0 :=
  of_native_maps core1487 DegreeOneSmallSpectrum738.graph DegreeOneSmallSpectrum527.graph
    sourceMap1487 fusedMap1487 sourceMap1487_checked fusedMap1487_checked
    DegreeOneSmallComparisons.comparison1487
#print axioms sourceMap1487_checked
#print axioms fusedMap1487_checked
#print axioms certified1487
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
