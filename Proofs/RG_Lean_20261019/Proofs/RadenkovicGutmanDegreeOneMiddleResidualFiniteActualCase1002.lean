/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1002 : Family 10 := level10.get ⟨896,by decide⟩
def sourceMap1002 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1002 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1002_checked : acceptsGraphIso
    (source (graph core1002) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2305.graph sourceMap1002=true := by decide +kernel
theorem fusedMap1002_checked : acceptsGraphIso
    (fused (graph core1002) (root 10) 2 2) DegreeTwoThreeSpectrum5761.graph fusedMap1002=true := by decide +kernel
theorem certified1002 : Certified (graph core1002) (root 10) 2 2 :=
  of_native_maps core1002 DegreeOneMiddleResidualSpectrum2305.graph DegreeTwoThreeSpectrum5761.graph
    sourceMap1002 fusedMap1002 sourceMap1002_checked fusedMap1002_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1002
#print axioms sourceMap1002_checked
#print axioms fusedMap1002_checked
#print axioms certified1002
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
