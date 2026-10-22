/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1039 : Family 10 := level10.get ⟨1015,by decide⟩
def sourceMap1039 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1039 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1039_checked : acceptsGraphIso
    (source (graph core1039) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1976.graph sourceMap1039=true := by decide +kernel
theorem fusedMap1039_checked : acceptsGraphIso
    (fused (graph core1039) (root 10) 2 2) DegreeTwoThreeSpectrum6013.graph fusedMap1039=true := by decide +kernel
theorem certified1039 : Certified (graph core1039) (root 10) 2 2 :=
  of_native_maps core1039 DegreeOneMiddleResidualSpectrum1976.graph DegreeTwoThreeSpectrum6013.graph
    sourceMap1039 fusedMap1039 sourceMap1039_checked fusedMap1039_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1039
#print axioms sourceMap1039_checked
#print axioms fusedMap1039_checked
#print axioms certified1039
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
