/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1030 : Family 10 := level10.get ⟨1000,by decide⟩
def sourceMap1030 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1030 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1030_checked : acceptsGraphIso
    (source (graph core1030) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1962.graph sourceMap1030=true := by decide +kernel
theorem fusedMap1030_checked : acceptsGraphIso
    (fused (graph core1030) (root 10) 2 2) DegreeTwoThreeSpectrum5976.graph fusedMap1030=true := by decide +kernel
theorem certified1030 : Certified (graph core1030) (root 10) 2 2 :=
  of_native_maps core1030 DegreeOneMiddleResidualSpectrum1962.graph DegreeTwoThreeSpectrum5976.graph
    sourceMap1030 fusedMap1030 sourceMap1030_checked fusedMap1030_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1030
#print axioms sourceMap1030_checked
#print axioms fusedMap1030_checked
#print axioms certified1030
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
