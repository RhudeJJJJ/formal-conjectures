/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1517 : Family 9 := level9.get ⟨251,by decide⟩
def sourceMap1517 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1517 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1517_checked : acceptsGraphIso
    (source (graph core1517) (root 9) 0 0) DegreeOneSmallSpectrum765.graph sourceMap1517=true := by decide +kernel
theorem fusedMap1517_checked : acceptsGraphIso
    (fused (graph core1517) (root 9) 0 0) DegreeOneSmallSpectrum561.graph fusedMap1517=true := by decide +kernel
theorem certified1517 : Certified (graph core1517) (root 9) 0 0 :=
  of_native_maps core1517 DegreeOneSmallSpectrum765.graph DegreeOneSmallSpectrum561.graph
    sourceMap1517 fusedMap1517 sourceMap1517_checked fusedMap1517_checked
    DegreeOneSmallComparisons.comparison1517
#print axioms sourceMap1517_checked
#print axioms fusedMap1517_checked
#print axioms certified1517
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
