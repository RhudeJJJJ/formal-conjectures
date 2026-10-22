/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1001 : Family 10 := level10.get ⟨895,by decide⟩
def sourceMap1001 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1001 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1001_checked : acceptsGraphIso
    (source (graph core1001) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2304.graph sourceMap1001=true := by decide +kernel
theorem fusedMap1001_checked : acceptsGraphIso
    (fused (graph core1001) (root 10) 2 2) DegreeTwoThreeSpectrum5760.graph fusedMap1001=true := by decide +kernel
theorem certified1001 : Certified (graph core1001) (root 10) 2 2 :=
  of_native_maps core1001 DegreeOneMiddleResidualSpectrum2304.graph DegreeTwoThreeSpectrum5760.graph
    sourceMap1001 fusedMap1001 sourceMap1001_checked fusedMap1001_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1001
#print axioms sourceMap1001_checked
#print axioms fusedMap1001_checked
#print axioms certified1001
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
