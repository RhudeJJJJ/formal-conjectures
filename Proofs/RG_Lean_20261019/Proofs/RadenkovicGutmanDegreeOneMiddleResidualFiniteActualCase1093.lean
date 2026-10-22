/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1093 : Family 10 := level10.get ⟨1147,by decide⟩
def sourceMap1093 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1093 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1093_checked : acceptsGraphIso
    (source (graph core1093) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2081.graph sourceMap1093=true := by decide +kernel
theorem fusedMap1093_checked : acceptsGraphIso
    (fused (graph core1093) (root 10) 2 2) DegreeTwoThreeSpectrum6284.graph fusedMap1093=true := by decide +kernel
theorem certified1093 : Certified (graph core1093) (root 10) 2 2 :=
  of_native_maps core1093 DegreeOneMiddleResidualSpectrum2081.graph DegreeTwoThreeSpectrum6284.graph
    sourceMap1093 fusedMap1093 sourceMap1093_checked fusedMap1093_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1093
#print axioms sourceMap1093_checked
#print axioms fusedMap1093_checked
#print axioms certified1093
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
