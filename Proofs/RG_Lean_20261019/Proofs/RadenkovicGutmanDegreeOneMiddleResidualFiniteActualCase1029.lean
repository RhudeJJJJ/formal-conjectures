/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1029 : Family 10 := level10.get ⟨999,by decide⟩
def sourceMap1029 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1029 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1029_checked : acceptsGraphIso
    (source (graph core1029) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1961.graph sourceMap1029=true := by decide +kernel
theorem fusedMap1029_checked : acceptsGraphIso
    (fused (graph core1029) (root 10) 2 2) DegreeTwoThreeSpectrum5974.graph fusedMap1029=true := by decide +kernel
theorem certified1029 : Certified (graph core1029) (root 10) 2 2 :=
  of_native_maps core1029 DegreeOneMiddleResidualSpectrum1961.graph DegreeTwoThreeSpectrum5974.graph
    sourceMap1029 fusedMap1029 sourceMap1029_checked fusedMap1029_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1029
#print axioms sourceMap1029_checked
#print axioms fusedMap1029_checked
#print axioms certified1029
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
