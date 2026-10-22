/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1015 : Family 10 := level10.get ⟨932,by decide⟩
def sourceMap1015 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1015 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1015_checked : acceptsGraphIso
    (source (graph core1015) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2318.graph sourceMap1015=true := by decide +kernel
theorem fusedMap1015_checked : acceptsGraphIso
    (fused (graph core1015) (root 10) 2 2) DegreeTwoThreeSpectrum5827.graph fusedMap1015=true := by decide +kernel
theorem certified1015 : Certified (graph core1015) (root 10) 2 2 :=
  of_native_maps core1015 DegreeOneMiddleResidualSpectrum2318.graph DegreeTwoThreeSpectrum5827.graph
    sourceMap1015 fusedMap1015 sourceMap1015_checked fusedMap1015_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1015
#print axioms sourceMap1015_checked
#print axioms fusedMap1015_checked
#print axioms certified1015
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
