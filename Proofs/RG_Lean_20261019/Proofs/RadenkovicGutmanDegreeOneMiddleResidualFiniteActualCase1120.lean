/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1120 : Family 10 := level10.get ⟨1252,by decide⟩
def sourceMap1120 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1120 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1120_checked : acceptsGraphIso
    (source (graph core1120) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2153.graph sourceMap1120=true := by decide +kernel
theorem fusedMap1120_checked : acceptsGraphIso
    (fused (graph core1120) (root 10) 2 2) DegreeTwoThreeSpectrum6495.graph fusedMap1120=true := by decide +kernel
theorem certified1120 : Certified (graph core1120) (root 10) 2 2 :=
  of_native_maps core1120 DegreeOneMiddleResidualSpectrum2153.graph DegreeTwoThreeSpectrum6495.graph
    sourceMap1120 fusedMap1120 sourceMap1120_checked fusedMap1120_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1120
#print axioms sourceMap1120_checked
#print axioms fusedMap1120_checked
#print axioms certified1120
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
