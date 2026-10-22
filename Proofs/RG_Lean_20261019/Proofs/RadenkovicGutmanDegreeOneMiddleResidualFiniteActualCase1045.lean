/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1045 : Family 10 := level10.get ⟨1032,by decide⟩
def sourceMap1045 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1045 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1045_checked : acceptsGraphIso
    (source (graph core1045) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1989.graph sourceMap1045=true := by decide +kernel
theorem fusedMap1045_checked : acceptsGraphIso
    (fused (graph core1045) (root 10) 2 2) DegreeTwoThreeSpectrum6047.graph fusedMap1045=true := by decide +kernel
theorem certified1045 : Certified (graph core1045) (root 10) 2 2 :=
  of_native_maps core1045 DegreeOneMiddleResidualSpectrum1989.graph DegreeTwoThreeSpectrum6047.graph
    sourceMap1045 fusedMap1045 sourceMap1045_checked fusedMap1045_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1045
#print axioms sourceMap1045_checked
#print axioms fusedMap1045_checked
#print axioms certified1045
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
