/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1019 : Family 10 := level10.get ⟨940,by decide⟩
def sourceMap1019 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1019 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1019_checked : acceptsGraphIso
    (source (graph core1019) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2322.graph sourceMap1019=true := by decide +kernel
theorem fusedMap1019_checked : acceptsGraphIso
    (fused (graph core1019) (root 10) 2 2) DegreeTwoThreeSpectrum5839.graph fusedMap1019=true := by decide +kernel
theorem certified1019 : Certified (graph core1019) (root 10) 2 2 :=
  of_native_maps core1019 DegreeOneMiddleResidualSpectrum2322.graph DegreeTwoThreeSpectrum5839.graph
    sourceMap1019 fusedMap1019 sourceMap1019_checked fusedMap1019_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1019
#print axioms sourceMap1019_checked
#print axioms fusedMap1019_checked
#print axioms certified1019
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
