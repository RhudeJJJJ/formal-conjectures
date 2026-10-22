/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1011 : Family 10 := level10.get ⟨927,by decide⟩
def sourceMap1011 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap1011 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1011_checked : acceptsGraphIso
    (source (graph core1011) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2314.graph sourceMap1011=true := by decide +kernel
theorem fusedMap1011_checked : acceptsGraphIso
    (fused (graph core1011) (root 10) 2 2) DegreeTwoThreeSpectrum5821.graph fusedMap1011=true := by decide +kernel
theorem certified1011 : Certified (graph core1011) (root 10) 2 2 :=
  of_native_maps core1011 DegreeOneMiddleResidualSpectrum2314.graph DegreeTwoThreeSpectrum5821.graph
    sourceMap1011 fusedMap1011 sourceMap1011_checked fusedMap1011_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1011
#print axioms sourceMap1011_checked
#print axioms fusedMap1011_checked
#print axioms certified1011
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
