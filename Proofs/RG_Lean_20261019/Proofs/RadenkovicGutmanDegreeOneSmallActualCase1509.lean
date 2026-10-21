/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1509 : Family 9 := level9.get ⟨239,by decide⟩
def sourceMap1509 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1509 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1509_checked : acceptsGraphIso
    (source (graph core1509) (root 9) 0 0) DegreeOneSmallSpectrum553.graph sourceMap1509=true := by decide +kernel
theorem fusedMap1509_checked : acceptsGraphIso
    (fused (graph core1509) (root 9) 0 0) DegreeOneSmallSpectrum552.graph fusedMap1509=true := by decide +kernel
theorem certified1509 : Certified (graph core1509) (root 9) 0 0 :=
  of_native_maps core1509 DegreeOneSmallSpectrum553.graph DegreeOneSmallSpectrum552.graph
    sourceMap1509 fusedMap1509 sourceMap1509_checked fusedMap1509_checked
    DegreeOneSmallComparisons.comparison1509
#print axioms sourceMap1509_checked
#print axioms fusedMap1509_checked
#print axioms certified1509
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
