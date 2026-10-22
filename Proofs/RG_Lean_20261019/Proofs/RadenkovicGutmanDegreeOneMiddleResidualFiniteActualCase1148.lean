/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1148 : Family 10 := level10.get ⟨1345,by decide⟩
def sourceMap1148 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1148 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1148_checked : acceptsGraphIso
    (source (graph core1148) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2220.graph sourceMap1148=true := by decide +kernel
theorem fusedMap1148_checked : acceptsGraphIso
    (fused (graph core1148) (root 10) 2 2) DegreeTwoThreeSpectrum6673.graph fusedMap1148=true := by decide +kernel
theorem certified1148 : Certified (graph core1148) (root 10) 2 2 :=
  of_native_maps core1148 DegreeOneMiddleResidualSpectrum2220.graph DegreeTwoThreeSpectrum6673.graph
    sourceMap1148 fusedMap1148 sourceMap1148_checked fusedMap1148_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1148
#print axioms sourceMap1148_checked
#print axioms fusedMap1148_checked
#print axioms certified1148
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
