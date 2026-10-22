/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1051 : Family 10 := level10.get ⟨1040,by decide⟩
def sourceMap1051 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1051 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1051_checked : acceptsGraphIso
    (source (graph core1051) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1997.graph sourceMap1051=true := by decide +kernel
theorem fusedMap1051_checked : acceptsGraphIso
    (fused (graph core1051) (root 10) 2 2) DegreeTwoThreeSpectrum6065.graph fusedMap1051=true := by decide +kernel
theorem certified1051 : Certified (graph core1051) (root 10) 2 2 :=
  of_native_maps core1051 DegreeOneMiddleResidualSpectrum1997.graph DegreeTwoThreeSpectrum6065.graph
    sourceMap1051 fusedMap1051 sourceMap1051_checked fusedMap1051_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1051
#print axioms sourceMap1051_checked
#print axioms fusedMap1051_checked
#print axioms certified1051
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
