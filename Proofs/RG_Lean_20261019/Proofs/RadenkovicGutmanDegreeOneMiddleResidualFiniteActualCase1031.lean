/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1031 : Family 10 := level10.get ⟨1001,by decide⟩
def sourceMap1031 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1031 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1031_checked : acceptsGraphIso
    (source (graph core1031) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1963.graph sourceMap1031=true := by decide +kernel
theorem fusedMap1031_checked : acceptsGraphIso
    (fused (graph core1031) (root 10) 2 2) DegreeTwoThreeSpectrum5979.graph fusedMap1031=true := by decide +kernel
theorem certified1031 : Certified (graph core1031) (root 10) 2 2 :=
  of_native_maps core1031 DegreeOneMiddleResidualSpectrum1963.graph DegreeTwoThreeSpectrum5979.graph
    sourceMap1031 fusedMap1031 sourceMap1031_checked fusedMap1031_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1031
#print axioms sourceMap1031_checked
#print axioms fusedMap1031_checked
#print axioms certified1031
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
