/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1015 : Family 8 := level8.get ⟨108,by decide⟩
def sourceMap1015 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap1015 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1015_checked : acceptsGraphIso
    (source (graph core1015) (root 8) 0 0) DegreeOneSmallSpectrum268.graph sourceMap1015=true := by decide +kernel
theorem fusedMap1015_checked : acceptsGraphIso
    (fused (graph core1015) (root 8) 0 0) DegreeOneSmallSpectrum270.graph fusedMap1015=true := by decide +kernel
theorem certified1015 : Certified (graph core1015) (root 8) 0 0 :=
  of_native_maps core1015 DegreeOneSmallSpectrum268.graph DegreeOneSmallSpectrum270.graph
    sourceMap1015 fusedMap1015 sourceMap1015_checked fusedMap1015_checked
    DegreeOneSmallComparisons.comparison1015
#print axioms sourceMap1015_checked
#print axioms fusedMap1015_checked
#print axioms certified1015
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
